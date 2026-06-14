# RandNLA CACM Bottleneck Ledger

This ledger is for formalization blockers that have survived repeated proof
attempts.  It is intentionally narrower than the theorem ledger: each row names
the exact Lean-facing theorem family that blocks a paper-level claim, the
dependencies that must close next, and the routes already rejected or deferred.

## Bottleneck Status

Resolved bottleneck entries are retained as audit history, but they no longer
block the current final gate. Active red bottlenecks are listed after the
resolved entries.

### ACTIVE RED: `LR.1-equation9-structural-relative-error`

Source target: CACM equation (9), the low-rank structural condition for
projection/sketch-based relative-error approximation.  The source statement
uses a right singular subspace split \(V_k,V_{k,\perp}\), singular blocks
\(\Sigma_k,\Sigma_{k,\perp}\), a sketching matrix \(Z\) with the source
full-rank condition on \(V_k^T Z\), and a unitarily invariant norm bound
involving \(\Sigma_{k,\perp}(V_{k,\perp}^T Z)(V_k^T Z)^+\).

Blocking theorem family:

- `columnSketchGramInverseProjector_sourceHeadTail_sourceSketchCoefficientRelativeResidualSurface_of_det_ne_zero`
  is the current closest exact-object surface.  It gives the concrete
  Gram-inverse projector result under visible hypotheses, but the paper-level
  theorem is still open because the source determinant, source-tail norm
  bounds, and SVD/Eckart--Young/unitarily invariant layers are not proved.
- The eventual source-facing theorem should replace the visible
  `det((A Z)^T(A Z)) != 0`, tail radius, projected-tail radius, and
  best-rank certificate assumptions by a rectangular SVD split, source
  \(V_k^T Z\) full-rank data, the equation-(9) singular-subspace norm
  expression, and a local best-rank/Eckart--Young certificate.

Closed dependencies:

- LR.1a--LR.1q exact-object rank, projector, Gram-inverse, source-coefficient,
  Moore--Penrose, and concrete Gram-inverse adapters are closed and validated.
- LR.1r closes the first algebraic component of D1:
  `sourceTailLeftOrthogonal`, `columnSketch_sourceSVDFactorMatrix`, the two
  cross-term cancellation theorems, and
  `columnSketchGram_sourceHeadTail_leftOrthogonal` prove the exact Gram split
  \((AZ)^T(AZ)=(H Z)^T(H Z)+(T Z)^T(T Z)\) under \(A=H+T\),
  \(H=U\Sigma V^T\), and \(U^T T=0\).
- LR.1s closes the PSD and determinant-preservation component of D1:
  `columnSketchGram_finitePSD` proves every exact column-sketch Gram is PSD,
  `matrix_det_ne_zero_of_posDef_add_posSemidef` proves that a
  positive-definite head Gram plus a PSD tail Gram has nonzero determinant, and
  `columnSketchGram_sourceHeadTail_det_ne_zero_of_head_posDef` applies this to
  the LR.1r source head-tail split.
- LR.1t closes the exact source-factor determinant side of D1:
  `matrix_transpose_mul_self_posDef_of_det_ne_zero` proves `R^T R` is positive
  definite from `det R != 0`, `columnSketchGram_posDef_of_sourceSVD_det_factors`
  derives the source-head sketch-Gram positive-definite certificate from
  `det(Sigma) != 0` and `det(V^T Z) != 0`, and
  `columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_det_factors`
  proves the full head-plus-tail sketch-Gram determinant nonzero under the
  exact source split and `U^T Tail=0`.
- LR.1bg closes the supplied-tail-factor path into that determinant theorem:
  `columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_det_factors_tail_factor_left_cross_zero`
  derives `U^T Tail=0` from an exact tail factorization and exact left-basis
  cross-orthogonality, then invokes the LR.1t determinant route.  This removes
  the raw source-tail orthogonality assumption from the determinant-facing
  theorem whenever exact tail factors are supplied.
- LR.1bj closes the diagonal singular-value block handoff into that same
  determinant route: `matrix_det_ne_zero_of_eq_diagonal_nonzero` proves
  `det(Sigma)=prod_a sigma_a != 0` from an exact diagonal `Sigma` with
  nonzero displayed entries, `matrix_det_ne_zero_of_eq_diagonal_pos` records
  positive singular values as a sufficient special case, and
  `columnSketchGram_sourceHeadTail_det_ne_zero_of_sourceSVD_diagonal_tail_factor_left_cross_zero`
  composes the diagonal determinant certificate with LR.1bg.
- LR.1bk propagates the same exact diagonal singular-block hypothesis through
  the source-facing sketch/projector route: the diagonal determinant certificate
  now feeds `sourceSVDSketchRightFactor`, the exact thin-factor certificate,
  source-head Gram determinant and positive-definiteness, head-plus-tail
  determinant bridge under exact `U^T Tail=0`, Gram-inverse and Moore--Penrose
  certificates, and the exact column-sketch projector surface.  This removes
  raw `det(Sigma) != 0` assumptions from the projector-facing source-SVD
  algebra when displayed diagonal singular values are supplied.
- LR.1bl carries that exact diagonal singular-block source through the
  concrete Gram-inverse projector residual and relative-residual surfaces.  The
  pure source-SVD residual forms no longer assume raw `det(Sigma) != 0`, and
  the source-head/tail forms derive the full sketch-Gram determinant internally
  from exact source-tail orthogonality, source orthonormality, diagonal nonzero
  `Sigma`, and `det(V^T Z) != 0`.  Tail/coupling norm radii, best-rank
  certificates, rectangular SVD/Eckart--Young construction, randomness-derived
  cross-term certificates, and computed non-probability routine certificates
  remain open.
- LR.1bm instantiates the exact source-head/tail tail and coupling radii for
  the diagonal source-SVD residual surface from the already-closed source-tail
  Frobenius and projected-tail certificates.  Under exact tail factors
  `Tail=Utail SigmaTail Vperp^T`, exact left/right orthogonality, row
  completeness, and a supplied exact CACM cross-term radius, the concrete
  Gram-inverse projector residual now has the visible scalar rate
  `2 * sqrt(1+eps^2) * ||SigmaTail||_F`, with a relative wrapper under a
  supplied best-rank comparison.  Rectangular SVD/Eckart--Young construction,
  randomness-derived cross-term certificates, and computed non-probability
  routine certificates remain open.
- LR.1bn composes LR.1bm with the exact source-head best-rank handoff.  A
  supplied Frobenius tail-optimality inequality for the exact split
  `A=U SigmaHead V^T+Tail` now instantiates `IsBestRankApproxFrob` for the
  exact source head, records `rho_F(A,U SigmaHead V^T)=||Tail||_F`, and gives
  the scalar LR.1bm residual bound relative to that exact source-head residual.
  The actual Eckart--Young/singular-value proof of tail optimality remains
  open.
- LR.1bo closes the first-class exact source-split certificate handoff:
  `DiagonalSourceSVDTailCertificate` packages the exact diagonal source
  head/tail split, exact tail factorization, left/right orthogonality,
  row-completeness, and nonzero diagonal head block.  Its wrappers feed that
  certificate directly into the LR.1bm scalar-rate rank surface and the LR.1bn
  tail-optimal relative surface.  Rectangular SVD existence, construction of
  the certificate from singular vectors/values, Eckart--Young tail optimality,
  randomness-derived cross-term bounds, and computed non-probability routine
  certificates remain open.
- LR.1br closes the next block-constructor layer below LR.1bo:
  `BlockDiagonalSourceSVDTailCertificate` assumes the primitive exact split
  `A=U SigmaHead V^T+Utail SigmaTail Vperp^T`, exact column orthonormality of
  `[U,Utail]`, exact column and row orthonormality of `[Vperp,V]`, and the
  diagonal nonzero head block.  It derives the component left/right
  orthogonality fields, constructs `DiagonalSourceSVDTailCertificate`, and
  feeds the constructed certificate into the scalar-rate and tail-optimal
  relative surfaces.  Actual rectangular SVD existence, singular-value
  positivity/order, Eckart--Young tail optimality, randomness, and computed
  non-probability routines remain open.
- LR.1bs closes a square-SVD split constructor below LR.1br:
  a supplied exact square SVD-style table `A=Ufull diag(sigma) Vfull^T`
  with exact orthogonal `Ufull,Vfull` now splits by `Fin.castAdd q` and
  `Fin.natAdd r` into source-head and source-tail blocks, constructs
  `BlockDiagonalSourceSVDTailCertificate`, and feeds the same scalar-rate and
  tail-optimal relative surfaces.  This is still an exact-object constructor:
  SVD existence, rectangular source-split construction, singular-value
  positivity/order beyond the visible head-nonzero condition, Eckart--Young,
  randomness, and computed non-probability routines remain open.
- LR.1bt closes the corresponding thin-rectangular split constructor:
  a supplied exact left table `Ufull : Fin m -> Fin (r+q) -> R` with exact
  column orthonormality, a supplied full right orthogonal table `Vfull`, and
  an exact representation `A=Ufull diag(sigma) Vfull^T` now split into the same
  source-head and source-tail blocks, construct
  `BlockDiagonalSourceSVDTailCertificate`, and feed the scalar-rate and
  tail-optimal relative surfaces.  This removes the square-left restriction
  from LR.1bs, but SVD existence, singular-value positivity/order beyond the
  visible head-nonzero condition, Eckart--Young, randomness, and computed
  non-probability routines remain open.
- LR.1bu closes the elementary source-style positivity handoff:
  strict positivity of every displayed head singular entry now supplies the
  nonzero-head field required by the square and thin-rectangular split
  constructors, and the corresponding scalar-rate and tail-optimal relative
  surfaces are available with `_head_pos` suffixes.  Singular-value ordering,
  rectangular SVD existence, Eckart--Young, randomness, and computed
  non-probability routines remain open.
- LR.1bv closes the exact source-tail Frobenius norm identity:
  if an exact source-SVD factor table `U Sigma V^T` has orthonormal left and
  right column factors, then its Frobenius norm equals `||Sigma||_F`.  The block
  source-tail certificate now supplies
  `||Utail SigmaTail Vperp^T||_F=||SigmaTail||_F`, the source-head residual
  equality with `||SigmaTail||_F`, and a block relative surface whose
  tail-optimality and scalar comparison hypotheses are stated directly with the
  displayed tail singular-value block.  Rectangular SVD existence,
  singular-value ordering, Eckart--Young tail optimality, randomness, and
  computed non-probability routines remain open.
- LR.1bw propagates LR.1bv to the supplied square and thin-rectangular SVD
  split surfaces.  Their tail norm identities, source-head residual identities,
  and relative equation-(9) wrappers are now stated directly with
  `||squareSVDTailDiagonal sigma||_F`, including strict-positive-head variants.
  This still assumes supplied exact SVD-style data; rectangular SVD existence,
  singular-value ordering, Eckart--Young tail optimality, randomness, and
  computed non-probability routines remain open.
- LR.1bx closes the direct D4 best-rank handoff for the same supplied square
  and thin-rectangular SVD-style data.  A visible sigma-tail optimality
  inequality now constructs `IsBestRankApproxFrob` for the square/thin source
  head without sketch/projector hypotheses.  The actual Eckart--Young theorem
  proving that inequality from ordered singular values remains open.
- LR.1by closes the exact right-Gram singular-value order/nonnegativity
  adapter for D3: `rectRightGram A=A^T A` is symmetric and PSD, its ordered
  Hermitian eigenvalues define nonnegative antitone singular-value squares,
  and their square roots define nonnegative antitone singular values with
  `sigma_j^2=lambda_j`.  This does not construct singular vectors, a
  rectangular SVD/source split, or the Eckart--Young tail-optimality theorem.
- LR.1bz closes the exact basis-indexed right-Gram eigenvector adapter for D3:
  mathlib's Hermitian eigenvector unitary for `A^T A` gives an orthogonal real
  eigenvector table, nonnegative basis-indexed singular values, the columnwise
  eigenvector equation, and the diagonalization `V^T(A^T A)V`.  This still does
  not identify the eigenbasis order with LR.1by's ordered zero-indexed
  singular-value sequence, construct a rectangular source split, or prove the
  Eckart--Young tail-optimality theorem.
- LR.1ca closes the full-positive basis-indexed reconstruction adapter for D3:
  if every basis-indexed singular value from LR.1bz is strictly positive, the
  left candidates `u_a=A v_a/tau_a` have orthonormal columns and reconstruct
  `A=sum_a u_a tau_a v_a^T`.  This is exact-object algebra for the
  full-positive case; zero singular values, ordered head/tail splitting, and
  Eckart--Young remain open.
- LR.1cb closes the next zero/rank-deficient sub-dependency: a zero
  basis-indexed singular value forces the exact projected column `A v_a` to be
  zero.  This reduces the zero singular-value part of D3 while leaving ordered
  head/tail splitting and Eckart--Young open.
- LR.1cc closes the removal of LR.1ca's full-positive hypothesis by defining
  zero-safe left candidates and proving the basis-indexed reconstruction
  without dividing by zero.  Ordered head/tail splitting and Eckart--Young
  remain open.
- LR.1cd closes the selected-index D3 reduction: LR.1cc's exact
  basis-indexed reconstruction is split into a selected-index head over an
  arbitrary finite set `s` and a complementary tail, and the head is factored
  through `Fin s.card`.  Identifying `s` with ordered top singular directions,
  rectangular SVD existence, and Eckart--Young remain open.
- LR.1ce closes the selected-head sketch-space bridge: for the selected
  right-Gram eigenvector sketch `Z_s`, `A Z_s` is the selected
  projected-column table and the LR.1cd selected head factors as
  `(A Z_s)V_s^T`.  This closes the exact
  `ColumnSketchHeadFactorization` dependency for arbitrary selected indices.
- LR.1cf closes the packaging of that selected split and selected-head
  factorization into the existing equation-(9) head/tail certificate surface.
  The proof closes only exact-object adapter algebra under
  explicit tail, projected-tail coupling, projector-through-sketch, and
  sketch-reproduction hypotheses.
- LR.1cg closes the transport of the selected rank bound from `s.card` to a
  displayed paper rank `k` under the explicit cardinality hypothesis
  `s.card = k`.  This is the cardinality layer of the ordered-selection
  handoff; it does not prove that `s` is the source-faithful ordered top-`k`
  set.
- LR.1ch closes the conversion of an injective selected-index map `Fin k ↪ Fin n`
  into the selected set consumed by LR.1cd--LR.1cg, with cardinality `k`
  proved internally.  This removes the separate cardinality hypothesis for
  embedding-based selected directions, while leaving the semantic ordered-top
  property open.
- LR.1bd closes the exact source-head rank certificate in D3:
  `sourceSVDFactorMatrixRankFactorization` factors the source head
  `U Sigma V^T` through the displayed source dimension `r`, and
  `sourceSVDFactorMatrix_rankAtMost` packages that factorization as a
  repository `RectRankAtMost` certificate.  This does not construct the
  rectangular SVD, source-tail orthogonality, Eckart--Young optimality, or
  computed SVD/projector/Gram layers.
- LR.1u reduces D2 to a coordinate residual norm bound:
  `sourceSketchResidualTail_leftFactor` factors
  `Tail-(Tail Z)(V^T Z)^{-1}V^T` through any displayed tail left basis
  `Utail`, and
  `frobNormRect_sourceSketchResidualTail_leftOrthonormalFactor` proves the
  ambient Frobenius norm equals the coordinate residual Frobenius norm when
  `Utail^T Utail=I`.
- LR.1v reduces the coordinate residual to the displayed right-tail source
  factor: `sourceRightBasisTranspose` represents `V_perp^T`,
  `rightSketchCrossGramRect` represents `V_perp^T Z`, and
  `sourceSketchResidualTail_sigmaRightBasisTranspose_explicit` proves the exact
  identity
  `Sigma_perp (V_perp^T-(V_perp^T Z)(V_k^T Z)^{-1}V_k^T)`.  The accompanying
  Frobenius theorem gives a visible non-sharp `||Sigma_perp||_F` bound.
- LR.1w closes the displayed right-orthogonal block products:
  `rightSketchCrossGramRectInvFactor` represents
  `(V_perp^T Z)(V_k^T Z)^{-1}`,
  `sourceRightResidual_mul_rightTailBasis_eq_id` proves
  `R_perp V_perp=I`, and
  `sourceRightResidual_mul_headRightBasis_eq_neg_invFactor` proves
  `R_perp V_k=-(V_perp^T Z)(V_k^T Z)^{-1}` under exact
  right-basis orthogonality/orthonormality hypotheses.
- LR.1x closes the Frobenius/right-orthogonal block identity after LR.1w:
  `finiteFrobNormSq_rectRightOrthonormal` proves generic sum-indexed
  right-orthonormal Frobenius invariance, `rightBasisBlock` represents
  `[V_perp,V_k]`, and
  `frobNormSqRect_sigma_sourceRightResidual_eq_block` proves
  `||Sigma R_perp||_F^2 = ||Sigma||_F^2 + ||Sigma (V_perp^T Z)(V_k^T Z)^{-1}||_F^2`
  under exact row-completeness of that block.
- LR.1bh closes the supplied block-orthonormality handoff for the right-basis
  fields: `rightBasisBlock_component_orthonormal_fields_of_col_orthonormal`
  derives \(V_\perp^T V_\perp=I\), \(V_k^T V_\perp=0\),
  \(V_\perp^T V_k=0\), and \(V_k^T V_k=I\) from exact column
  orthonormality of `[V_perp,V_k]`, while
  `rightBasisBlock_complete_sum_of_row_orthonormal` derives the row-complete
  identity from exact row orthonormality.  The wrapper
  `frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq_of_rightBasisBlock_orthonormal`
  feeds these fields directly into the source residual bound.
- LR.1bi closes the reverse assembly handoff from separate component
  SVD-style right-basis fields to the block certificate consumed by LR.1bh:
  `rightBasisBlock_col_orthonormal_of_component_orthonormal_fields` and
  `rightBasisBlock_col_row_orthonormal_of_component_fields` assemble exact
  column and row orthonormality of `[V_perp,V_k]`, and
  `frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq_of_component_block_assembly`
  routes the same cross-term radius through the block theorem.
- LR.1y closes the source-faithful Frobenius cross-term certificate handoff:
  `frobNormRect_sigma_sourceRightResidual_le_sqrt_one_add_eps_sq` proves that
  the exact CACM structural condition
  `||Sigma (V_perp^T Z)(V_k^T Z)^{-1}||_F <= eps ||Sigma||_F`,
  with `eps >= 0`, implies
  `||Sigma (V_perp^T-(V_perp^T Z)(V_k^T Z)^{-1}V_k^T)||_F <=
  sqrt(1+eps^2)||Sigma||_F` under the LR.1x right-basis hypotheses.
- LR.1z closes the ambient source-tail Frobenius handoff:
  `frobNormRect_sourceSketchResidualTail_sourceSVDTail_le_sqrt_one_add_eps_sq`
  composes LR.1u's left-orthonormal ambient-to-coordinate residual equality,
  LR.1v's `Sigma_perp V_perp^T` coordinate residual factorization, and LR.1y's
  source cross-term certificate to prove the ambient residual-tail bound
  `||Tail-(Tail Z)(V_k^T Z)^{-1}V_k^T||_F <= sqrt(1+eps^2)||Sigma||_F`
  from supplied exact source-tail SVD-factor data.
- LR.1aa closes the Frobenius projector-applied/coupling tail handoff:
  `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq`
  first proves that symmetric idempotent finite row multipliers are
  Euclidean- and Frobenius-nonexpansive, then instantiates that contraction for
  an exact column-sketch orthogonal projector `P=(A Z)C`, and finally composes
  it with LR.1z to prove
  `||P(T-(T Z)(V_k^T Z)^{-1}V_k^T)||_F <= sqrt(1+eps^2)||Sigma||_F`
  from supplied exact source-tail, cross-term, and Moore--Penrose certificates.
- LR.1ab closes the transpose-action spectral certificate handoff for D2:
  `frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_transpose_rectOpNorm2Le`
  proves that the exact right-acting operator certificate
  `rectOpNorm2Le (finiteTranspose ((V_perp^T Z)(V_k^T Z)^{-1})) eps`
  implies
  `||Sigma (V_perp^T Z)(V_k^T Z)^{-1}||_F <= eps||Sigma||_F`, and
  `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq_of_transpose_rectOpNorm2Le`
  composes that certificate with LR.1aa to prove the projected Moore--Penrose
  coupling-tail bound without separately assuming the Frobenius cross-term
  certificate.
- LR.1ac closes the ordinary non-transposed operator-certificate handoff for
  D2: `rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le` proves that an exact
  rectangular operator certificate for `M` implies the needed transpose-action
  certificate for `M^T`; `frobNormRect_sigma_rightSketchCrossGramRectInvFactor_le_of_rectOpNorm2Le`
  and
  `frobNormRect_preconditionRows_sourceSketchResidualTail_sourceSVDTail_moorePenrose_le_sqrt_one_add_eps_sq_of_rectOpNorm2Le`
  instantiate this for `M=(V_perp^T Z)(V_k^T Z)^{-1}` and then compose through
  LR.1aa.
- LR.1ad closes a D5 computed-cross-factor perturbation transfer for the same
  equation-(9) cross term: if a computed non-probability factor `Mhat` has
  ordinary operator radius `eps` and the exact analysis factor
  `M=(V_perp^T Z)(V_k^T Z)^{-1}` is within Frobenius radius `tau`, then the
  exact Frobenius cross term has radius `eps+tau`, and the projected
  Moore--Penrose coupling-tail bound has radius
  `sqrt(1+(eps+tau)^2)`.  Concrete FP routines still have to instantiate
  `Mhat`, the operator certificate, and the perturbation radius.
- LR.1ae closes the matching D5 entrywise-error wrapper: if a concrete routine
  supplies a uniform entrywise certificate
  `|M_ij-Mhat_ij| <= eta`, then
  `frobNormRect_le_sqrt_mul_nat_of_entry_abs_le` gives the Frobenius radius
  `sqrt(q*r)eta`, so LR.1ad yields the cross-term radius
  `eps+sqrt(q*r)eta` and the projected Moore--Penrose radius
  `sqrt(1+(eps+sqrt(q*r)eta)^2)`.  Concrete FP routines still have to prove
  that entrywise budget and the computed operator certificate.
- LR.1af closes the D5 component-certificate layer for forming that computed
  cross factor: if `Xhat` approximates `V_perp^T Z`, `Yhat` approximates
  `(V_k^T Z)^{-1}`, and `Mhat` is the rounded product `Xhat*Yhat`, with
  row/column contraction radii `alpha`, `beta`, and product radius `rho`, then
  the entrywise radius required by LR.1ae is `alpha+beta+rho`.  Concrete FP
  routines still have to instantiate the dot-product, inverse, final product,
  and computed-operator certificates.
- LR.1ag closes the concrete rectangular cross-gram dot-product layer inside
  LR.1af: `Xhat = flRightSketchCrossGramRect fp Vperp Z` is the repository
  floating-point matrix product `fl_matMul((V_perp)^T,Z)`, with entry budget
  `gamma(fp,n) sum_j |Vperp_{ja}| |Z_{jb}|`.  Contracting this visible budget
  against the exact inverse columns supplies the LR.1af `alpha` term.  Concrete
  FP routines still have to instantiate the inverse-factor budget, final
  rounded-product budget, computed-operator certificate, square cross-gram
  input to the inverse, and computed SVD/projector/Gram layers.
- LR.1ah closes the analogous concrete square cross-gram input certificate:
  `flRightSketchCrossGram fp V Z = fl_matMul((V)^T,Z)` has entry budget
  `gamma(fp,n) sum_j |V_{ja}| |Z_{jb}|`, and a uniform `omega` cap gives
  `||V^T Z - fl((V^T)Z)||_F <= sqrt(r*r) omega`.  This is the visible input
  perturbation certificate that a later inverse routine theorem can consume;
  the inverse perturbation theorem itself remains open.
- LR.1ai closes the algebraic propagation from an inverse routine entrywise
  certificate to the computed cross-factor radius.  If
  `|nonsingInv(V_k^T Z)-Yhat| <= eta` and
  `sum_b |fl((V_perp^T Z))_{ab}| <= chi`, then the LR.1af right component
  budget is `chi*eta`; the composed radius is
  `eps+sqrt(q*r)(alpha+chi*eta+rho)`.  A concrete inverse algorithm still has
  to prove the entrywise `eta` certificate.
- LR.1aj closes the concrete final rounded-product routine for the same D5
  component chain.  The computed product
  `flRightSketchCrossGramRectInvFactorProduct fp Xhat Yhat =
  fl_matMul(Xhat,Yhat)` has entry budget
  `gamma(fp,r) sum_b |Xhat_ab| |Yhat_bc|`.  When this visible product budget
  is at most `rho`, LR.1ai applies with the same radius
  `eps+sqrt(q*r)(alpha+chi*eta+rho)`.  The final product arithmetic is now
  instantiated; the concrete inverse algorithm's `eta` certificate and the
  computed operator certificate remain open.
- LR.1ak closes a deterministic operator-certificate handoff for that computed
  product: a visible certificate
  `||fl(fl((V_perp^T)Z)Yhat)||_F <= eps` implies the ordinary rectangular
  operator certificate required by LR.1aj.  The same cross-term and projected
  radii `eps+sqrt(q*r)(alpha+chi*eta+rho)` are preserved.  This does not
  derive such a Frobenius certificate from randomness or from an inverse
  algorithm; it just replaces an abstract operator predicate by a concrete
  Frobenius certificate surface for the computed product.
- LR.1al closes a deterministic source for that product Frobenius certificate
  from visible product absolute sums.  If
  `sum_b |Xhat_ab||Yhat_bc| <= kappa` and the same final product
  `fl_matMul` budget is at most `rho`, then
  `|fl(Xhat Yhat)_{ac}| <= kappa+rho` and
  `||fl(Xhat Yhat)||_F <= sqrt(q*r)(kappa+rho)`.  Any displayed `eps` above
  this value supplies the computed-product operator certificate consumed by
  LR.1ak and preserves the same equation-(9) radii.
- LR.1am closes a deterministic source for the inverse entrywise `eta`
  certificate from a Higham-style perturbed inverse contract.  If
  `(A+DeltaA)Yhat=I`, `|DeltaA| <= epsInv |A|`, and
  `epsInv * sum |A^{-1}| |A| |Yhat| <= eta`, then
  `|nonsingInv(A)-Yhat| <= eta`; specializing
  `A=rightSketchCrossGram V Z` feeds LR.1ai.  This does not yet formalize a
  concrete inversion loop that produces `DeltaA` and `Yhat`.
- LR.1an closes a Method-A LU inverse-solve source for the same entrywise
  `eta` certificate.  The computed inverse
  `methodAComputedInverse fp r L_hat U_hat` is built columnwise from
  `fl_forwardSub` and `fl_backSub`; `LUBackwardError r (V_k^T Z) L_hat U_hat
  (gamma fp r)`, nonzero triangular diagonals, and the visible Method-A
  forward-error budget imply
  `|nonsingInv(V_k^T Z)-methodAComputedInverse fp r L_hat U_hat| <= eta`.
  This narrows the remaining concrete inversion obligation to the LU
  factor-generation/backward-error certificate for the square cross Gram.
- LR.1ao closes the computed-input transfer layer for that Method-A route.
  If a concrete LU factorization is certified for
  `flRightSketchCrossGram fp V Z` at coefficient `epsLU`, and the
  square-cross-Gram input dot-product error is bounded by
  `mu * sum_l |L_hat b l||U_hat l c|`, then the exact analysis matrix
  `V_k^T Z` inherits an LU certificate at coefficient `epsLU+mu`.  Method A
  then uses the visible coefficient `(epsLU+mu)+2*gamma+gamma^2` in the
  inverse-sensitivity budget and feeds the existing equation-(9) wrappers.
  The remaining LU obligation is now the concrete factor-generation theorem
  for `flRightSketchCrossGram`, not the computed-input transfer.
- LR.1ap closes the certificate-level Doolittle factor-generation bridge for
  the rounded square cross Gram.  `DoolittleLU.to_LUBackwardError` proves that
  a Doolittle recurrence certificate for `flRightSketchCrossGram fp V Z`
  supplies `LUBackwardError r (flRightSketchCrossGram fp V Z) L_hat U_hat
  (gamma fp r)`.  Combining this with LR.1ao gives the Method-A coefficient
  `(gamma fp r+mu)+2*gamma fp r+gamma fp r^2` and feeds the product-sum and
  projected Moore--Penrose equation-(9) wrappers.  The remaining dense-LU
  obligation is constructing the `DoolittleLU` witness from an executable
  routine, not proving recurrence-to-backward-error.
- LR.1aq closes the first norm-abstract equation-(9) surface.  `RectNormLike`
  exposes only nonnegativity and the triangle inequality, and the new
  `Equation9ResidualNormCertificate` / `Equation9HeadTailSketchNormCertificate`
  wrappers prove rank, residual, and relative-residual statements for any
  supplied norm-like functional.  This does not instantiate a concrete
  unitarily invariant norm or prove the singular-value/orthogonal-invariance
  steps; it makes those D2/D4 dependencies explicit.
- LR.1ar closes the concrete Frobenius instance of that norm-generic surface.
  `frobRectNormLike` packages the repository rectangular Frobenius norm as a
  `RectNormLike`, transports Frobenius residual/best-rank/head-tail
  certificates into the norm-generic API, exposes the existing left/right
  orthogonal invariance facts for this instance, and specializes the generic
  rank/residual and relative-residual wrappers back to Frobenius.  This still
  does not prove the general all-unitarily-invariant norm API, singular-value
  comparison, or Eckart--Young construction.
- LR.1ba closes the supplied-norm API layer for unitarily invariant norms.
  `UnitaryInvariantRectNormLike` extends `RectNormLike` with exact left/right
  orthogonal invariance fields, `frobUnitaryInvariantRectNormLike` instantiates
  that interface for Frobenius, and the unitary-norm equation-(9) wrappers
  reuse the norm-generic rank/residual and relative-residual surfaces.  This
  still does not prove singular-value comparison or construct Eckart--Young
  best-rank certificates from rectangular SVD data.
- LR.1as closes the dense-loop Doolittle witness surface for the D5 Method-A
  route.  `flDoolittleUEntry`, `flDoolittleLNumerator`, and
  `flDoolittleLEntry` expose the literal rounded dense-Doolittle row and
  column folds.  `DoolittleDenseLoopCertificate.to_DoolittleLU` proves that
  visible residual-compression budgets for those literal outputs are sufficient
  to construct the compact `DoolittleLU` recurrence certificate, and the new
  RandNLA wrappers feed the same computed-input Method-A and projected
  Moore--Penrose equation-(9) bounds from that dense-loop certificate.  A
  concrete proof of the residual-compression budgets under pivot/no-cancellation
  conditions remains open.
- LR.1at closes the absolute-budget handoff immediately below LR.1as.  A
  concrete implementation can now prove ordinary absolute residual budgets for
  the literal dense-Doolittle folds, prove the dominance inequalities
  `BU <= gamma(fp,r)|Uhat|` and `BL <= gamma(fp,r)|Lhat*Ukk|`, and obtain the
  dense-loop residual-compression certificate, `DoolittleLU`,
  `LUBackwardError`, Method-A inverse-entry radius, and projected equation-(9)
  bound.  The remaining implementation work is now the source proof of those
  absolute budgets and dominance inequalities under a specified pivot and
  no-cancellation regime.
- LR.1au closes the rounded-product subtraction-accumulation source for part of
  those absolute budgets.  The generic theorem
  `fl_sub_sum_error_init_abs_residual_le` and the Doolittle specializations
  `flDoolittleUEntry_rounded_residual_abs_le` and
  `flDoolittleLNumerator_rounded_residual_abs_le` bound the literal upper fold
  and lower numerator fold against the rounded products actually subtracted.
  Remaining D5 fold-budget sources are the transfer from rounded products to
  exact products, the lower rounded division/pivot multiplication budget, and
  the dominance inequalities needed by LR.1at.
- LR.1av closes the rounded-product to exact-product transfer for those
  Doolittle folds.  `fl_mul_abs_sub_mul_le` supplies the primitive
  multiplication-error bound, and the upper/lower-numerator specializations add
  the explicit `fp.u * sum |Lhat*Uhat|` term.  Remaining D5 fold-budget sources
  are the `Fin k` to masked-`Fin n` packaging, the lower rounded division/pivot
  multiplication budget, and the dominance inequalities needed by LR.1at.
- LR.1aw closes the `Fin k` to masked-`Fin n` packaging.  The generic bridge
  `finMaskedPrefixSum_eq_finSum` reindexes prefix sums into the exact recurrence
  shape used by `DoolittleDenseLoopAbsBudgetCertificate`, and the two Doolittle
  wrappers expose masked exact-product residual budgets for upper entries and
  lower numerators.  Remaining D5 fold-budget sources are lower rounded
  division/pivot multiplication and dominance inequalities.
- LR.1bp closes the exact-target gap transfer for the same D5 route.  The
  exact pre-rounded Doolittle targets and their literal rounded-fold residual
  budgets now transfer source-facing exact-target gaps to the stored upper
  exact-product margin, stored lower exact-product margin, and stronger lower
  numerator margin, then instantiate
  `DoolittleDenseLoopAbsBudgetCertificate`.
- LR.1bq audits that exact-target route and rules it out as the next ordinary
  source route in nondegenerate floating-point regimes.  Triangle gives
  `|T^U_kj| <= |A_kj|+E^U_kj` and `|T^L_ik| <= |A_ik|+E^L_ik`, so the LR.1bp
  exact-target gaps force the added FP excess terms `uE+R` or `R^N+R^L` to be
  nonpositive.  Thus LR.1bp remains a valid conditional transfer, but proving
  those exact-target gaps from a concrete pivot/off-diagonal/no-cancellation
  invariant is not a viable positive D5 dependency unless the excess is
  degenerate.
- The current probability convention is locked: sampling probabilities and
  sampling laws are exact mathematical inputs; probability-construction FP
  errors are deliberately out of scope unless the user reopens them.

Open dependencies:

- D1. The exact source-factor head-plus-tail sketch Gram determinant route is
  closed by LR.1r--LR.1t.  Instantiating the displayed source certificates from
  an actual rectangular SVD/source split remains tracked under D3.
- D2. Prove the remaining general unitarily invariant variants after
  LR.1u--LR.1ac's
  reductions, now starting from the
  exact displayed factor
  \(\Sigma_{k,\perp}(V_{k,\perp}^T-(V_{k,\perp}^T Z)(V_k^T Z)^+V_k^T)\).  The
  ambient unprojected Frobenius source-tail bound is closed for supplied exact
  source-tail SVD-factor data and a supplied Frobenius cross-term certificate.
  The Frobenius projector-applied/coupling tail bound is also closed for
  supplied exact orthogonal-projector/Moore--Penrose certificates, and the
  transpose-action operator-2 certificate now implies the needed Frobenius
  cross-term certificate.  LR.1ac also closes the non-transposed ordinary
  operator-certificate handoff for the same cross factor.  LR.1aq now closes
  the norm-generic head/tail theorem surface once a norm-like functional and
  its visible tail/coupling bounds are supplied, and LR.1ar instantiates that
  surface for the concrete rectangular Frobenius norm with explicit
  orthogonal-invariance handoffs, and LR.1ba closes the supplied-norm API for
  unitarily invariant norm certificates.  The next D2 dependencies are
  singular-value comparison theorems for the same cross term
  \(\Sigma_{k,\perp}(V_{k,\perp}^T Z)(V_k^T Z)^+\), randomness-derived
  certificates for that exact operator condition, and the D3/D5 source and
  implementation layers.
- D3. Build or reuse rectangular SVD existence and source split certificates.
  LR.1bd now supplies the exact source-head rank factorization once
  \(U,\Sigma,V\) are given.  LR.1be now proves that an exact split
  \(A=U\Sigma V^T+T\) makes the source-head residual exactly \(\|T\|\), and
  packages the source head as a best-rank certificate when the tail-optimality
  inequality is supplied.  LR.1bf now derives \(U^T T=0\) from a supplied
  tail factorization \(T=U_\perp\Sigma_\perp V_\perp^T\) and supplied
  left-basis cross-orthogonality \(U^T U_\perp=0\).  LR.1bg composes that
  supplied-tail-factor route into the determinant theorem, so D1 no longer
  needs a raw \(U^T T=0\) hypothesis when exact tail factors are present, and
  LR.1bj closes the diagonal determinant handoff from an exact diagonal
  singular block with nonzero displayed singular values, and LR.1bk propagates
  that diagonal determinant source through the exact source sketch/projector
  certificates.
  LR.1bh reduces the right-basis component fields to exact column/row
  orthonormality of the concatenated block \([V_\perp,V_k]\), and LR.1bi proves
  the reverse assembly direction from separate SVD-style component fields and
  row completeness to that block certificate.  LR.1bo now packages the exact
  diagonal source split, tail factorization, left/right fields, and diagonal
  nonsingular head block into `DiagonalSourceSVDTailCertificate`, with wrappers
  into the scalar-rate rank and tail-optimal relative surfaces.  LR.1br derives
  that certificate from primitive block decomposition data and exact
  orthonormality of `[U,Utail]` and `[Vperp,V]`.  LR.1bs further derives the
  same block certificate from a supplied exact square SVD-style table by
  splitting full source indices into head and tail blocks.  LR.1bt removes the
  square-left restriction by accepting a thin rectangular left table with exact
  column orthonormality and a full right orthogonal basis.  LR.1bu then reduces
  the leading-positive singular-value field to the nonzero-head field consumed
  by those constructors.  LR.1by closes the exact right-Gram eigenvalue
  nonnegativity/order adapter used to define singular-value magnitudes from
  \(A^T A\).  LR.1bz closes the exact basis-indexed right-Gram eigenvector
  table and diagonalization adapter, and LR.1ca closes the full-positive
  basis-indexed SVD-style reconstruction from that table.  LR.1cc removes the
  full-positive hypothesis with zero-safe left candidates.  LR.1cd partitions
  that reconstruction into an arbitrary selected-index head and complementary
  tail and packages the selected head rank bound through `Fin s.card`.  LR.1ce
  proves that this selected head lies in the exact selected eigenvector sketch
  space.  The remaining D3 work after that bridge is the ordered rectangular
  SVD/source-split existence theorem, including ordered head/tail basis
  handoff and the displayed diagonal singular block from the ordered
  right-Gram magnitudes.
- LR.1cf closes the small-adapter step packaging the arbitrary selected
  right-Gram split from LR.1cd and the selected sketch-space bridge from
  LR.1ce into the generic equation-(9) head/tail rank/residual surface.
  This leaves the same source-SVD, Eckart--Young, randomness, and
  computed non-probability routine obligations open, but it removes one
  remaining adapter between D3 and the D1 residual certificate API.
- LR.1cg closes the rank-index adapter moving the LR.1cf rank conclusion
  from `|s|` to the paper's displayed rank `k` under a visible cardinality
  equality.  The semantic ordered-top-direction theorem remains the next
  genuine D3 route choice after this handoff.
- LR.1ch closes the embedding-selection adapter: define the selected set
  from an injective finite index map and feed its internally proved cardinality
  into LR.1cg.  The next route choice after this is the semantic ordering
  theorem tying such an embedding to the ordered right-Gram singular values.
- LR.1ci closes that semantic ordering certificate handoff: the proof exposes
  the exact certificate equating embedding-selected basis singular values with
  the ordered right-Gram singular values on the first `k` displayed indices,
  derives selected square/order facts, and composes that certificate with the
  already-closed embedding rank/residual surface.  Constructing the certificate
  remains the true D3 order foundation.
- LR.1cj closes construction of that certificate from mathlib's own Hermitian
  matrix spectral reindexing: both the basis-indexed `eigenvalues` and
  `eigenvectorBasis` are obtained from ordered `eigenvalues₀` by the same
  `Fintype.equivOfCardEq` route.  This removes the arbitrary-looking basis-order
  gap for the right-Gram table used in LR.1cd--LR.1ci.
- LR.1ck closes the exact ordered head/complement comparison for the constructed
  top-`k` embedding: an unselected basis index has inverse ordered coordinate
  at least `k`, so every selected top singular value dominates every unselected
  basis-indexed singular value.  This supplies a necessary spectral-index
  ingredient for an Eckart--Young/tail-optimality route, while leaving the
  actual rectangular SVD/source split and tail-optimality proof open.
- LR.1cl closes the exact selected-head positivity handoff from a kth-singular-
  value positivity hypothesis: if the last displayed top-`k` ordered singular
  value is positive, all constructed selected head singular values are positive
  and therefore nonzero.  This feeds the source-SVD determinant/diagonal routes
  without proving rectangular SVD existence or Eckart--Young.
- LR.1cm closes the exact selected left-basis orthonormality ingredient for the
  constructed ordered top-`k` block: positivity from LR.1cl lets the zero-safe
  left candidates be rewritten as normalized projected columns, whose dot
  products reduce to the right-Gram diagonalization identity.  This feeds a
  future ordered source split, while leaving tail factor construction,
  right-basis completeness, rectangular SVD existence, Eckart--Young, and
  computed non-probability SVD/singular-vector/projector/Gram/sketch routine
  certificates open.
- LR.1cn closes the exact ordered source-head factorization: the selected
  right-Gram head induced by the constructed top-`k` embedding is
  \(U_{\mathrm{ord}}\Sigma_{\mathrm{ord}}V_{\mathrm{ord}}^T\), with exact
  head-left and head-right column orthonormality under the same kth singular
  value positivity hypothesis.  The complementary tail factor, row completeness
  for the full right-basis split, rectangular SVD/source split, Eckart--Young,
  and computed non-probability SVD/singular-vector/projector/Gram/sketch routine
  certificates remain open.
- LR.1co closes the exact ordered complement-tail factorization and source
  split: the complement of the constructed top-`k` selected set is enumerated
  as \(q=|s_{\mathrm{ord}}^c|\), the complementary tail is
  \(U_{\mathrm{tail}}\Sigma_{\mathrm{tail}}V_{\mathrm{tail}}^T\),
  \(V_{\mathrm{tail}}\) has exact orthonormal columns, and the ordered source
  head plus this ordered source tail reconstructs \(A\).  This intentionally
  does not claim \(U_{\mathrm{tail}}\) is an orthonormal rectangular-SVD tail
  basis in the presence of zero tail singular values; nullspace completion,
  full right-basis row completeness, Eckart--Young, and computed
  non-probability routine certificates remain open.
- LR.1cp closes the exact ordered right-basis block fields: selected-set and
  complement enumeration lemmas prove the head/tail right-column cross terms are
  zero and prove row completeness from the full right-Gram eigenbasis row
  identity.  Thus the constructed block \([V_{\mathrm{tail}},V_{\mathrm{ord}}]\)
  has exact column orthonormality and row completeness.  Nullspace-completed
  tail-left orthonormality, Eckart--Young, randomness, and computed
  non-probability routine certificates remain open.
- LR.1cq closes the constructed ordered split-to-block-certificate adapter:
  the ordered source head/tail split and constructed right-basis block now
  instantiate `BlockDiagonalSourceSVDTailCertificate` once the remaining
  left-block and head-nonzero fields are supplied.  The component-left
  positivity variant uses the kth ordered singular-value positivity theorem to
  discharge the ordered head nonzero and head-left orthonormality fields,
  leaving exactly the tail-left orthonormality and head-tail left
  cross-orthogonality/nullspace-completion obligations visible, along with
  Eckart--Young, randomness, and computed non-probability routine
  certificates.
- LR.1cr closes the constructed ordered head-tail left cross field:
  kth ordered singular-value positivity and selected/complement disjointness
  prove `U_ord^T U_tail = 0` for the zero-safe constructed tables.  The
  constructed ordered block-certificate route now exposes only the tail-left
  orthonormality/nullspace-completion field on the left block, plus
  Eckart--Young, randomness, and computed non-probability routine certificates.
- LR.1cs closes the positive-complement tail-left branch: if every
  complement-enumerated singular value is strictly positive, then the
  constructed complement-tail zero-safe left table satisfies
  `U_tail^T U_tail = I_q`, and the ordered block source-SVD certificate is
  fully instantiated under kth head positivity.  The zero-tail/nullspace-
  completion branch remains open, as do Eckart--Young, randomness, and
  computed non-probability routine certificates.
- LR.1ct formally rules out the raw zero-safe table for the zero-tail branch:
  if a complement singular value is zero, the corresponding tail-left column is
  identically zero and has self-dot `0`, contradicting the required diagonal
  value `1`.  Therefore the remaining zero-tail route must construct a
  nullspace-completed orthonormal tail-left basis rather than reuse the raw
  zero-safe table.  Eckart--Young, randomness, and computed non-probability
  routine certificates remain open.
- LR.1cu closes the replacement-tail-left adapter for that remaining zero-tail
  route: any replacement tail-left table that agrees with the zero-safe table
  on nonzero complement singular directions gives the same exact source-tail
  factor, because zero singular-value columns are erased by the diagonal tail
  block.  Under kth head positivity, replacement-tail orthonormality, and
  replacement head-tail cross fields, the constructed ordered block source-SVD
  certificate follows.  The actual nullspace-completed replacement basis,
  Eckart--Young, randomness, and computed non-probability routine certificates
  remain open.
- LR.1cv closes a necessary dimension guard for the same route: any
  sum-indexed column-orthonormal family in \(\mathbb R^m\) has at most `m`
  columns, so the full left block `[U,Utail]` in
  `BlockDiagonalSourceSVDTailCertificate` forces `r+q <= m`.  For a full
  right-Gram source split with `r+q=n`, a nullspace-completed replacement-basis
  construction must expose the tall/thin condition `n <= m` or switch to a
  rectangular SVD surface with only the appropriate number of left columns.
  The replacement basis, Eckart--Young, randomness, and computed
  non-probability routine certificates remain open.
- LR.1cw closes the exact-object orthonormal-completion core under the exposed
  dimension/embedding surface: any partially specified orthonormal column family
  in \(\mathbb R^m\) can be extended to a full `m x m` orthonormal table, and an
  embedded head/tail block specialization gives a replacement `Utail` preserving
  specified tail columns while making `[U,Utail]` column-orthonormal.  The
  remaining nullspace-completion dependency is to instantiate the partial set
  with all head columns plus the ordered nonzero complement-tail directions and
  then compose the result with LR.1cu's source-factor agreement adapter.
  Eckart--Young, randomness, and computed non-probability routine certificates remain
  open.
- LR.1cx closes that ordered instantiation/composition step under a supplied
  embedding into `Fin m`: the partial set is now exactly all ordered head
  columns plus the nonzero complement-tail directions; the zero-safe columns are
  partial-orthonormal on that set; completion yields a replacement `Utail`
  agreeing on nonzero tail directions, full `[U_ord,Utail]` column
  orthonormality, and an ordered `BlockDiagonalSourceSVDTailCertificate` through
  LR.1cu.  The remaining D3/D4 bottleneck has moved to Eckart--Young/tail
  optimality and the implementation-facing computed non-probability routine
  certificates; randomness-derived cross-term/product certificates also remain
  open.
- LR.1cy closes the first D4 min-max dependency: every
  `RectRankAtMost m (r+1) r B` has a nonzero vector
  `x : Fin (r+1) -> Real` with `B x = 0` in the repository finite-sum
  matrix-vector convention.  The proof uses the explicit factorization through
  `Fin r` plus mathlib finite-dimensional rank-nullity and has passed the full
  Lean/lookup/PDF gate.  The remaining
  Eckart--Young work is now the spectral singular-value lower-bound step, then
  the Frobenius tail-optimality assembly and rectangular SVD/source-split
  construction.
- LR.1cz closes the kernel-to-residual D4 target: the LR.1cy kernel vector
  plus local Frobenius matrix-vector domination now prove a min-max residual
  lower-bound adapter from a supplied vector-action source inequality
  `sigma ||x||_2 <= ||A x||_2`.  The theorem has passed the full
  Lean/lookup/PDF gate.  The remaining spectral work is narrowed to proving
  that vector-action lower bound from the ordered singular block.
- LR.1da closes that narrowed generic spectral target.  The planned generic
  adapter now proves the LR.1cz vector-action hypothesis from exact
  left-orthonormal columns, an exact square right-orthogonal block, and
  diagonal singular entries bounded below by `sigma`, and it has passed the
  full Lean/lookup/PDF gate.  Ordered singular-value instantiation and computed
  non-probability SVD/basis certificates remain separate.
- LR.1db closes the supplied SVD-style specialization of LR.1da.  The square
  and thin-rectangular full diagonal source factors inherit the vector-action
  lower bound directly from the displayed singular-entry lower bound.  This
  has passed the full Lean/lookup/PDF gate, but it still does not prove
  singular-value ordering, Eckart--Young optimality, SVD/source-split
  existence, randomness-derived certificates, or computed non-probability
  SVD/projector/product routines.
- LR.1dc closes the composition of the supplied diagonal lower-action wrappers
  with the LR.1cz min-max residual adapter.  It proves the exact rank-`r`
  residual lower bound for one `(r+1)` source block under visible diagonal
  lower-entry hypotheses, passed the full Lean/lookup/PDF gate, and leaves
  full tail optimality as the next D4 target.
- LR.1dd closes the ordered-source instantiation of that one-block lower bound:
  the constructed ordered top-`r+1` right-Gram head, the named ordered
  diagonal, and an identity right block force residual at least the last
  selected ordered singular value.  This passed the full Lean/lookup/PDF gate
  and remains exact-object spectral infrastructure, not the full Frobenius
  tail-optimality theorem and not a computed SVD/singular-vector/projector/Gram/
  sketch/product certificate.
- LR.1de closes the next one-step Eckart--Young adapter:
  `frobNorm_squareSVDTailDiagonal_one` identifies the `q=1` tail diagonal norm
  with the last ordered singular value, and
  `isBestRankApproxFrob_of_rectRightGramOrderedHeadDiagonal_succ` uses LR.1dd
  to make the ordered first-`r` truncation a best rank-`r` approximant for the
  ordered top-`r+1` coefficient block.  The scoped Lean/lookup/full-build/PDF
  gate passed.  This remains exact-object one-step infrastructure, not the
  full multi-tail Frobenius theorem or a computed
  SVD/singular-vector/projector/Gram/sketch/product certificate.
- LR.1df closes the next multi-tail algebra dependency:
  `frobNormSq_squareSVDTailDiagonal_eq_sum` and
  `frobNorm_squareSVDTailDiagonal_eq_sqrt_sum` prove the general `q`
  tail-diagonal Frobenius square formula and its square-root norm form.  This
  prepares the displayed tail norm used by the full Eckart--Young theorem,
  and its scoped Lean/lookup/full-build/PDF gate passed, while the
  q-dimensional min-max/tail-optimality lower bound remains the next real D4
  foundation.
- LR.1dg closes the q-dimensional rank-nullity dependency:
  `rectRankRightFactorMap_ker_finrank_ge` proves that the right-factor kernel
  of a rank-`r` competitor on `r+q` coordinates has dimension at least `q`,
  and `rectRankFactorization_matrix_rightKernel_of_rightFactor_ker` pushes
  kernel membership through `RectRankFactorization` to get competitor
  annihilation.  The scoped Lean/lookup/full-build/PDF gate passed.  This
  closes only the q-dimensional right-kernel infrastructure; vector selection,
  tail Frobenius lower bounds, and full Eckart--Young optimality remain
  separate D4 dependencies.
- LR.1dh closes vector selection inside the right-factor kernel:
  apply `exists_linearIndependent_of_le_finrank` to the kernel subtype supplied
  by LR.1dg, then push each selected vector through the stored factorization to
  get entrywise competitor annihilation via
  `rectRankFactorization_exists_rightKernelFamily`.  The
  scoped Lean/lookup/full-build/PDF gate passed.  This closes only the selected
  kernel-family infrastructure; the
  q-dimensional tail lower-bound argument and full Eckart--Young optimality
  remain separate D4 dependencies.
- LR.1di strengthens the selected-family dependency to an orthonormal `Fin q`
  family inside the Euclidean-coordinate right-factor kernel.  The proof uses
  a Euclidean version of the right-factor map, rank-nullity, `stdOrthonormalBasis`,
  and the same coordinate annihilation bridge.  Scoped Lean, lookup, full-build,
  axiom-audit, PDF text, and PDF render validation passed.  This prepares the
  trace/Rayleigh tail lower-bound route, but it is not itself the full
  Eckart--Young theorem.
- LR.1dj closes the next exact-object residual-energy step: finite Bessel
  inequality gives Frobenius domination for orthonormal right probes, and the
  result is specialized to the LR.1di right-kernel family.  Scoped Lean,
  lookup, full-build, axiom-audit, PDF text, and PDF render validation passed.
  The source-side tail-energy lower bound remains open.
- LR.1dk closes the source-side diagonal tail-energy engine.  The visible-gap
  diagonal mass-transfer theorem for orthonormal right frames passed scoped
  Lean, lookup, full-build, axiom-audit, PDF text, and PDF render validation.
  Ordered-singular-value instantiation and right-basis transport remain
  separate D4 dependencies.
- LR.1dl closes the positive-head ordered diagonal gap instantiation: the last
  displayed head square supplies the LR.1dk gap under antitone ordered
  singular-value squares.  Focused Lean, lookup, full-build, axiom-audit, PDF
  text, and PDF render validation passed.  The zero-head case and right-basis
  transport remain separate D4 dependencies.
- LR.1dm closes the zero-head diagonal source-tail energy companion: with no
  head coordinates, a full orthonormal `q`-frame gives coordinate masses
  exactly one and hence diagonal action energy equal to the tail square sum.
  Focused Lean, lookup, full-build, axiom-audit, PDF text, and PDF render
  validation passed.  Right-basis transport remains a separate D4 dependency.
- LR.1dn is closed for the combined ordered diagonal source-tail theorem:
  the proof splits internally on `r = 0` versus `0 < r`, reuses LR.1dm and
  LR.1dl, and has passed focused Lean, lookup, full-build, axiom-audit, PDF
  text, and PDF render validation.  Right-basis transport remains the next
  separate D4 dependency.
- LR.1do is closed for exact source-factor right-basis transport:
  `V^T` carries an exact orthonormal probe frame to another exact orthonormal
  frame, `||U diag(sigma) V^T x||_2^2` equals the transported diagonal energy
  by exact left column orthonormality of `U`, and the summed statement composes
  with LR.1dn.  Focused Lean, lookup, full-build, axiom-audit, PDF text, and
  PDF render validation passed.  Computed SVD/singular-vector/projector/Gram/
  sketch/product certificates remain D5 obligations and probabilities/laws
  remain exact mathematical inputs.
- LR.1dp is closed for the q-dimensional Eckart--Young lower-bound bridge:
  LR.1dj's residual-side selected orthonormal right-kernel frame and LR.1do's
  source-side lower bound prove every exact rank-at-most-`r` competitor has
  squared residual at least the ordered tail-square sum, plus the square-root
  norm form.  Focused Lean, lookup, full-build, axiom-audit, PDF text, and PDF
  render validation passed.  Source-split construction and D5 computed-object
  certificates remain open.
- LR.1dq is closed for the ordered supplied-SVD best-rank adapter:
  LR.1dp plus the tail-diagonal Frobenius identity now supplies the
  tail-optimality hypothesis in the existing square and thin supplied-SVD
  best-rank constructors, after the diagonal source-factor expansion aligns
  the paper-style SVD sum with the repository source-factor surface.  Focused
  Lean, lookup, full-build, axiom-audit, PDF text, and PDF render validation
  passed.  This remains exact-object D4 assembly only; computed
  SVD/singular-vector/projector/Gram/sketch/product certificates are still D5
  obligations, and probabilities/laws remain exact mathematical inputs.
- LR.1dr is closed for the ordered supplied-SVD relative surface propagation:
  LR.1dq now removes the raw tail-optimality hypothesis from the existing
  square/thin sigma-tail relative-residual wrappers, while leaving exact
  determinant, cross-term, and scalar relative-comparison hypotheses visible.
  Focused Lean, lookup, full-build, axiom-audit, PDF text, and PDF render
  validation passed.  This remains exact-object D4 theorem-surface propagation
  only; computed SVD/singular-vector/projector/Gram/inverse/sketch/product
  certificates and randomness-derived cross-term certificates remain open.
- LR.1ds is closed for the constructed ordered replacement-tail rank/residual
  surface: the nullspace-completed ordered source split from LR.1cx now feeds
  the exact block-certificate equation-(9) rank surface, yielding a concrete
  Gram-inverse column-sketch projector residual radius
  `2 * sqrt(1 + eps^2) * ||Sigma_tail||_F` under visible
  `det(V_ord^T Z) != 0` and exact cross-term hypotheses.  Focused Lean,
  lookup, full-build, axiom-audit, PDF text, and PDF render validation passed.
  This is exact-object D3 progress only; the relative/Eckart--Young conclusion,
  randomness-derived cross-term certificates, and computed non-probability
  SVD/singular-vector/projector/Gram/inverse/sketch/product certificates remain
  open.
- LR.1dt is closed and fully validated for the constructed ordered
  replacement-tail relative surface with visible D4 hypotheses: the same
  nullspace-completed ordered source split feeds the block-certificate
  sigma-tail relative theorem once exact tail optimality and scalar comparison
  are supplied.  Focused Lean, lookup, aggregate RandNLA build, full Lake
  build, marker scan, axiom audit, PDF compile, PDF text, and PDF render
  validation passed.  This removes the source-split handoff from the relative
  surface, but the actual Eckart--Young tail-optimality proof,
  randomness-derived cross-term certificates, and computed non-probability
  SVD/singular-vector/projector/Gram/inverse/sketch/product certificates remain
  open.
- LR.1du is closed and fully validated for the constructed ordered
  tail-diagonal Frobenius expansion: the generic exact diagonal identity
  `||diag(sigma)||_F^2 = sum_c sigma_c^2` now specializes to
  `rectRightGramOrderedTailSingularDiagonal A hk`, rewriting LR.1dt's
  `||Sigma_tail||_F` as the square root of the complement singular-square sum.
  Focused Lean, lookup, full Lake build, marker scan, axiom audit, PDF compile,
  PDF text, PDF render, and root/docs PDF sync validation passed.  This prepares
  the remaining Eckart--Young residual lower-bound transport, but does not prove
  that lower bound, derive randomness, or certify computed non-probability
  SVD/singular-vector/projector/Gram/inverse/sketch/product routines.
- LR.1dv is closed and fully validated for the constructed ordered
  head-tail cardinality bridge: any embedding-selected top set satisfies
  `k + |S^c| = n`, and the constructed ordered tail-index type specializes
  this to `k + q = n`.  This is the Fin/cardinality dependency needed before
  the q-dimensional Eckart--Young lower-bound theorem can be transported to the
  original `n`-column ordered source split.  Focused Lean, lookup, full Lake
  build, marker scan, axiom audit, PDF compile, PDF text, PDF render, and
  root/docs PDF sync validation passed.  It does not build the column
  permutation/equivalence transport, prove the residual lower bound, derive
  randomness, or certify computed non-probability
  SVD/singular-vector/projector/Gram/inverse/sketch/product routines.
- LR.1dw is closed and fully validated for the source-factor gap lower-bound bridge:
  the q-dimensional source-side and residual lower-bound theorems now require
  only a visible head-tail separator `eta`, not global singular-square
  antitonicity.  This is the correct route for the constructed ordered
  complement-tail enumeration, which is selected as the complement of the top
  set and need not be internally sorted.  Focused Lean, lookup, full Lake
  build, marker scan, axiom audit, PDF compile, PDF text, PDF render, and
  root/docs PDF sync validation passed.  The remaining proof still must instantiate the gap from the constructed
  right-Gram top set, build the original-column reindexing/equivalence
  transport, prove the residual lower-bound discharge for LR.1dt's
  tail-optimality hypothesis, derive randomness, and certify computed
  non-probability SVD/singular-vector/projector/Gram/inverse/sketch/product
  routines.
- LR.1dx is closed and fully validated for the constructed ordered head-tail
  square gap: the last selected top singular square supplies the visible
  separator `eta`; every selected head square is at least `eta`, and every
  complement-tail square is at most `eta`.  The complement tail still need not
  be internally sorted.  Focused Lean, focused LowRankApprox build, lookup, full
  Lake build, marker scan, axiom audit, PDF compile, PDF text, PDF render, and
  root/docs PDF sync validation passed.  Remaining obligations are the
  original-column reindexing/equivalence transport, LR.1dt tail-optimality
  discharge, randomness-derived cross-term certificates, and computed
  non-probability SVD/singular-vector/projector/Gram/inverse/sketch/product
  routine certificates.  Sampling probabilities and laws remain exact
  mathematical inputs.
- LR.1ea is fully validated for exact cross-domain column-equivalence
  transport.  `rectReindexCols` pulls an `n`-column matrix back along an exact
  `Fin p ≃ Fin n`; explicit rank factorizations, rank-at-most certificates,
  Frobenius norms, and Frobenius residuals transport across this equivalence.
  The constructed LR.1dz wrappers specialize the result to the ordered
  head-plus-complement-tail column equivalence.  Focused Lean, focused
  LowRankApprox build, lookup, full Lake build, marker scan, axiom audit, PDF
  compile, PDF text, PDF render, and root/docs PDF sync validation passed.
  This clears the residual/rank reindexing algebra needed before the LR.1dt
  tail-optimality discharge, but it does not prove that discharge, derive
  randomness, or certify computed non-probability SVD/singular-vector/projector/
  Gram/inverse/sketch/product routine certificates.  Sampling probabilities and
  laws remain exact mathematical inputs.
- LR.1eb is fully validated for the constructed ordered tail-optimality
  discharge.  The head-first `Fin(k+q)` source blocks are assembled from the
  replacement-tail certificate; the pulled-back right block is orthogonal; the
  assembled source factor is equal to the column-reindexed original matrix; and
  the gap lower-bound plus Frobenius tail expansion proves
  `||rectRightGramOrderedTailSingularDiagonal A hk||_F <= lowRankResidualFrob A B`
  for every exact rank-at-most-`k` competitor `B`.  The hopt-free wrapper feeds
  this into the LR.1dt relative surface.  Focused Lean, focused LowRankApprox
  build, lookup, full Lake build, marker scan, axiom audit, PDF
  compile/text/render checks, and root/docs PDF sync passed.  Remaining
  obligations are randomness-derived cross-term certificates, the scalar
  relative comparison, and computed non-probability
  SVD/singular-vector/projector/Gram/inverse/sketch/product routine
  certificates.  Sampling probabilities and laws remain exact mathematical
  inputs.
- LR.1ec is fully validated for the scalar-relative cleanup after LR.1eb.  The
  theorem `two_sqrt_one_add_sq_mul_tail_le_of_scalar` proves that the cleaner
  coefficient condition `2 * sqrt (1 + eps^2) <= rho` implies the product-form
  comparison after multiplying by any nonnegative tail radius, and the ordered
  replacement-tail wrapper applies it to the exact constructed tail Frobenius
  norm.  Focused Lean, focused Preconditioning repair/build, focused
  LowRankApprox build, lookup, full Lake build, marker scan, axiom audit, PDF
  compile/text/render checks, and root/docs PDF sync passed.  Remaining
  obligations are randomness-derived cross-term certificates and computed
  non-probability SVD/singular-vector/projector/Gram/inverse/sketch/product
  routine certificates.  Sampling probabilities and laws remain exact
  mathematical inputs.
- LR.1dz is fully validated for the constructed ordered
  head-plus-complement-tail column equivalence.  The map from
  `Fin k ⊕ rectRightGramOrderedTailIndex hk` to `Fin n` sends heads through
  `rectRightGramOrderedTopEmbedding hk` and tails through the complement
  enumeration; injectivity follows from selected/complement disjointness and
  surjectivity from the selected-or-complement split.  Composing with
  `finSumFinEquiv` gives the exact `Fin (k+q) ≃ Fin n` transport.  Focused
  Lean, focused LowRankApprox build, lookup, full Lake build, marker scan,
  axiom audit, PDF compile/text/render checks, and root/docs PDF sync passed.
  This closes the constructed equivalence dependency but does not discharge
  LR.1dt tail optimality, derive randomness, or certify computed
  non-probability SVD/singular-vector/projector/Gram/inverse/sketch/product
  routine certificates.  Sampling probabilities and laws remain exact
  mathematical inputs.
- LR.1dy is fully validated for exact column-permutation transport: explicit
  rank factorizations, rank-at-most certificates, and Frobenius residuals are
  invariant under exact column reindexing when source and competitor are
  reindexed together.  Focused Lean, focused LowRankApprox build, lookup, full
  Lake build, marker scan, axiom audit, PDF compile/text/render checks, and
  root/docs PDF sync passed.  This clears the generic transport dependency
  needed before building the constructed
  head-plus-complement-tail `Fin (k+q) ≃ Fin n` equivalence.  It does not
  discharge LR.1dt tail optimality, derive randomness, or certify computed
  non-probability SVD/singular-vector/projector/Gram/inverse/sketch/product
  routine certificates.  Sampling probabilities and laws remain exact
  mathematical inputs.
- D4. Prove the Eckart--Young/best-rank Frobenius certificate and the needed
  unitarily invariant norm infrastructure.  LR.1be reduces construction of
  `IsBestRankApproxFrob` for the displayed source head to the visible
  tail-optimality inequality, but does not prove that inequality from singular
  values.  LR.1bn composes that supplied tail-optimality inequality through the
  LR.1bm scalar-rate theorem, so the remaining D4 gap is now the genuine
  Eckart--Young/singular-value proof of tail optimality rather than the
  theorem-surface handoff.
- D5. Add implementation-facing certificates for all computed non-probability
  quantities used by any final algorithm theorem: computed SVD/singular
  vectors/bases, cross products, Gram matrices, inverses, coefficient tables,
  projectors, matrix products, sketch products, and downstream solver inputs.
  LR.1ad closes only the abstract computed-cross-factor transfer once a routine
  supplies `Mhat`, an operator certificate, and a Frobenius perturbation
  certificate.  LR.1ae closes the entrywise-error-to-Frobenius wrapper once a
  routine supplies `|M_ij-Mhat_ij| <= eta`.  LR.1af closes the component
  algebra that derives such an entrywise radius from computed cross-gram,
  inverse, and product component budgets.  LR.1ag instantiates the rectangular
  cross-gram component with the concrete repository `fl_matMul` dot-product
  bound.  LR.1ah instantiates the square cross-gram inverse input with the same
  concrete dot-product model.  LR.1ai closes the finite-sum adapter from an
  entrywise inverse-routine certificate to the computed-factor `beta` term; it
  still leaves the concrete inverse algorithm proof of `eta` and the final
  product routine.  LR.1aj instantiates that final product routine with the
  repository `fl_matMul` dot-product model.  LR.1ak shows that a visible
  Frobenius certificate for that computed product supplies the needed operator
  predicate.  LR.1al supplies that Frobenius certificate from a uniform
  product absolute-sum budget plus the same final product `rho` budget.  LR.1am
  supplies the inverse `eta` hypothesis from a perturbed-inverse certificate
  using the existing `ideal_forward_error` theorem, and LR.1an supplies the
  same hypothesis from the Method-A LU computed inverse once an
  `LUBackwardError` certificate for `V_k^T Z` is visible.  LR.1ao transfers an
  LU certificate for `flRightSketchCrossGram fp V Z` to the exact
  `V_k^T Z` certificate with a visible input coefficient `mu`, and LR.1ap
  supplies that rounded-input LU certificate from a `DoolittleLU` recurrence
  contract.  LR.1as exposes the literal dense-Doolittle fold surface and proves
  that visible residual-compression budgets for its outputs construct the
  needed `DoolittleLU` witness.  LR.1at lowers that obligation to ordinary
  absolute residual budgets plus dominance inequalities against
  `gamma(fp,r)|Uhat|` and `gamma(fp,r)|Lhat*Ukk|`.  LR.1au closes the
  subtraction-accumulation source for those budgets when measured against the
  rounded products, and LR.1av transfers those fold budgets to exact-product
  residuals with an explicit product-roundoff term.  LR.1aw packages those
  `Fin k` sums into the masked `Fin n` certificate shape.  LR.1ax charges the
  lower rounded division and multiplication by the computed pivot under a
  visible nonzero-pivot hypothesis and the literal lower-entry equality.
  LR.1ay packages the resulting explicit upper/lower source budgets into
  `DoolittleDenseLoopAbsBudgetCertificate` once the visible dominance
  inequalities are supplied.  LR.1az proves a componentwise no-cancellation
  route for those dominance inequalities: upper work/product terms bounded by
  the stored upper entry and lower work/product/numerator terms bounded by the
  stored lower-pivot product instantiate the same certificate after the
  `gamma(k)+u` and `gamma(k)+2u` absorptions.  LR.1bb proves the product-growth
  handoff from exact-product no-cancellation margins to those rounded-work and
  exact-product component bounds, paying the explicit `(1+u_fp)` factor for
  products actually computed by the dense Doolittle fold.  LR.1bc proves the
  lower rounded-numerator dominance handoff from an exact-product numerator
  margin: the displayed margin absorbs the exact lower work, the
  exact-product residual budget, the `(1+u_fp)` rounded-product growth factor,
  and the primitive multiplication budget, yielding
  `doolittleLNumeratorAbs <= |L_hat i k * U_hat k k|`.  LR.1bp then shifts
  those stored-entry margins back to exact pre-rounded Doolittle target gaps,
  paying the literal rounded-product, subtraction-fold, lower division, and
  computed-pivot residual budgets.  LR.1bq proves that this exact-target source
  route is triangle-obstructed when the FP excess is positive.  The remaining
  D5 obligations are therefore proving stored-entry/component dominance by a
  genuinely non-vacuous implementation invariant, changing the compression
  surface if stored-entry dominance is too strong, adding sharper or
  randomness-derived product certificates when the absolute-sum route is not
  the desired one, and the computed SVD/projector/Gram layers.

Rejected/deferred routes:

- Treating the exact `ColumnSketchMoorePenroseCertificate` or the exact
  Gram-determinant hypothesis as if it were the source theorem is rejected.
  Those are closed adapters, not proof of the paper-level condition.
- Treating LR.1bp exact-target gaps as the next ordinary D5 source route is
  rejected in nondegenerate FP regimes by LR.1bq: the triangle upper bound on
  `|A-sum products|` makes the displayed exact-target gaps imply nonpositive
  FP excess.
- Adding probability-law perturbation or computed-probability repair is
  deferred by user convention; probabilities and laws remain exact inputs.

Next concrete dependency target:

- Continue D3 with actual rectangular SVD/source-split existence feeding
  LR.1br/LR.1bt, then D4 with Eckart--Young tail optimality and D2 with
  singular-value comparison for the exact cross term.  In parallel, continue D5
  only through a non-vacuous stored-entry/component-dominance source, a revised
  compression surface, or sharper/randomness-derived product norm certificates
  beyond LR.1al.

### RESOLVED: `A3.4-SRHT-row-norm-concentration`

`A3.4-SRHT-row-norm-concentration` is closed for the Algorithm 3
SRHT random-projection uniformization row.  The source-level target is the SRHT
Hadamard/sign route behind Tropp, "Improved analysis of the subsampled
randomized Hadamard transform," Lemma 3.3 and Theorem 3.1: for an
orthonormal-column matrix \(U\), a randomized sign matrix followed by a flat
Hadamard-style orthogonal transform should make the maximum preconditioned row
norm small with high probability, yielding approximately uniform leverage
scores before later row sampling.

Blocking theorem family:

- Closed in explicit-`t` form by
  `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_sqrt_add_sq_ge_one_sub_m_exp_m_t_sq_div_eight`.
- The source-level leverage uniformization is closed in explicit-`t` form by
  `rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_sqrt_add_sq_div_nat_ge_one_sub_m_exp_m_t_sq_div_eight`
  and its delta-budget/logarithmic wrappers.
- The exact Algorithm 3 sampling composition is closed by
  `signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht`.

Closed dependencies:

- deterministic square-orthogonal preprocessing preserves Frobenius norm,
  `HasOrthonormalColumns`, and the equation (6) denominator;
- sign diagonals preserve orthogonality;
- the finite Rademacher sign-vector law and probability-one signed-preprocessing
  support event are closed;
- finite first/second moment identities and the flat-Hadamard expected row norm
  theorem are closed;
- the source-directed expected Euclidean row-norm step from Tropp's proof is
  closed by
  `rademacherTraceProbability_expectationReal_sqrt_rowNormSq_signedHadamard_le`;
- the deterministic orthonormal-column contraction and signed-Hadamard
  Lipschitz input are closed by
  `hasOrthonormalColumns_vecNorm2Sq_mul_vec_eq`,
  `hasOrthonormalColumns_transpose_mul_vecNorm2Sq_le`,
  `abs_vecNorm2_sub_le_vecNorm2_sub`, and
  `signedHadamard_row_vecNorm2_lipschitz`;
- the deterministic signed-Hadamard row-norm convexity input is closed by
  `FiniteVecConvex`, `vecNorm2_linear_combination_convex`, and
  `signedHadamard_row_vecNorm2_convex`;
- the deterministic affine scaling from Ledoux's \([0,1]^m\) theorem to
  Tropp's Rademacher-sign theorem is closed by `FiniteVecLipschitzWith`,
  `unitCubeToRademacherVec`,
  `finiteVecConvex_scaled_unitCubeToRademacher`, and
  `finiteVecLipschitzWith_scaled_unitCubeToRademacher`;
- the finite-probability Chernoff optimizer from a centered subgaussian MGF
  bound to a one-sided `exp(-t^2/(2 sigma^2))` tail is closed by
  `FiniteProbability.eventProb_real_le_ge_one_sub_exp_of_mgf_bound` and
  `FiniteProbability.eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_subgaussian_mgf`;
- the finite MGF/Herbst calculus substrate for the Ledoux route is closed by
  `FiniteProbability.expectationReal_exp_pos`,
  `FiniteProbability.hasDerivAt_expectationReal_exp_mul`,
  `FiniteProbability.hasDerivAt_log_expectationReal_exp_mul`,
  `FiniteProbability.entropyReal`,
  `FiniteProbability.entropyReal_exp_mul_eq`,
  `FiniteProbability.log_mgf_differential_le_of_entropyReal_exp_mul_le`,
  `FiniteProbability.log_mgf_div_sub_quadratic_antitoneOn_of_differential_le`,
  `FiniteProbability.tendsto_log_mgf_div_nhdsGT_zero`,
  `FiniteProbability.log_mgf_le_mean_add_quadratic_of_differential_le`,
  `FiniteProbability.log_mgf_le_mean_add_quadratic_of_entropyReal_exp_mul_le`,
  `FiniteProbability.expectationReal_exp_centered_le_exp_of_log_mgf_le`, and
  `FiniteProbability.eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_log_mgf_bound`,
  and
  `FiniteProbability.eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_entropyReal_exp_mul_le`;
- the finite product-law Fubini and entropy chain-rule algebra needed for
  product-measure tensorization is closed by
  `FiniteProbability.prod_expectationReal_eq`,
  `FiniteProbability.prod_expectationReal_fst_eq`, and
  `FiniteProbability.entropyReal_prod_eq_expectation_entropyReal_add_entropyReal_expectation`;
- the unbiased Bernoulli coordinate law and exact coordinate expectation/entropy
  formulas are closed by `FiniteProbability.boolUniformProbability`,
  `FiniteProbability.boolUniformProbability_prob`,
  `FiniteProbability.boolUniformProbability_expectationReal`, and
  `FiniteProbability.entropyReal_boolUniformProbability_eq`;
- the scalar two-point entropy bound and the positive-function fair-Bernoulli
  coordinate log-Sobolev inequality are closed by
  `FiniteProbability.twoPointEntropy_le_sq_sub_div_of_pos` and
  `FiniteProbability.entropyReal_boolUniformProbability_sq_le_sq_sub_of_pos`;
- the finite `L2` Cauchy-Schwarz/triangle/reverse-triangle bridge needed to
  control the conditional-second-moment section norm is closed by
  `FiniteProbability.abs_expectationReal_mul_le_sqrt_mul_sqrt`,
  `FiniteProbability.sqrt_expectationReal_sq_add_le`,
  `FiniteProbability.abs_sqrt_expectationReal_sq_sub_le_sqrt_expectationReal_sub_sq`,
  and the Bernoulli-coordinate wrapper
  `FiniteProbability.boolUniformProbability_abs_sqrt_expectationReal_sq_sub_le_sqrt_expectationReal_sub_sq`;
- the first one-coordinate tensorization peel-off is closed by
  `FiniteProbability.entropyReal_prod_boolUniformProbability_sq_le_coordinate_add_entropy`,
  which bounds `Ent_{P x Bool}(g^2)` by the Bernoulli-coordinate squared
  difference plus the still-open entropy of the conditional second moment;
- the abstract Bernoulli-product induction lift is closed by
  `FiniteProbability.entropyReal_prod_boolUniformProbability_sq_le_lifted_diff_sum_add`;
  it lifts an existing entropy-gradient bound on `P` to `P x Bool` using the
  `L2` section-norm bridge;
- the concrete `RademacherTrace m` cube split/iteration layer is closed by
  `rademacherTraceProbability_entropyReal_sq_le_sum_flip`, after adding
  `rademacherTraceFlip`, the `Fin.snoc` mass/expectation/entropy transport
  lemmas, and the flip/snoc compatibility lemmas;
- the weak Markov/union all-row theorem
  `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_ge_one_sub_delta`
  is closed, but it has Markov scaling and does not close Tropp's lemma;
- the exact signed-linear-form MGF factorization
  `rademacherTraceProbability_expectationReal_exp_sum_mul_sign_eq_prod` and
  one-sided exponential-Markov skeleton
  `rademacherTraceProbability_eventProb_sum_mul_sign_le_ge_one_sub_exp_mul_prod`
  are closed;
- the scalar cosh/Hoeffding dependency, one-sided and two-sided signed-linear-
  form tails, the flat-Hadamard coordinate variance proxy, and the weaker
  coordinate-Hoeffding all-row theorem
  `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_ge_one_sub_sum_exp_sq_bound`
  are closed;
- the scoped equation-(6) coordinate-Hoeffding leverage-probability lift
  `rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_ge_one_sub_delta`
  is closed;
- the uniform row one-step foundations
  `uniformRowOuterGramSample`, `uniform_rowOuterGramSample_mean_eq_id`,
  `finitePSD_uniformRowOuterGramSample`, and
  `uniformRowOuterGramSample_finiteLoewnerLe_of_leverageScoreProb_le` are
  closed;
- the signed-Hadamard row-norm coordinate-flip algebra and deterministic
  positive-flip self-bounding dependency are closed by
  `vecNorm2_inv_smul_self_of_pos`,
  `vecInnerProduct_inv_smul_self_eq_norm`,
  `vecNorm2_sub_le_inner_unit_diff`,
  `rademacherSignVector_flip_self`,
  `rademacherSignVector_flip_of_ne`,
  `rademacherSignVector_sub_flip`,
  `signedHadamard_row_inner_sq_sum_eq_inv_mul`,
  `signedHadamard_row_vec_sub_flip`, and
  `signedHadamard_row_vecNorm2_positive_flip_sq_sum_le`;
- the positive-drop exponential-tilt bridge and source-sharp one-row/all-row
  SRHT row-norm theorems are closed by
  `real_exp_half_sub_sq_le_quarter_mul_sq_mul_exp_of_le`,
  `real_exp_half_sub_sq_le_lam_sq_quarter_pair_pos`,
  `rademacherTraceProbability_flip_tilt_sq_sum_bound_of_pointwise_posdiff_sq_sum_le`,
  `rademacherTraceProbability_flip_tilt_sq_sum_bound_signedHadamard_row_vecNorm2`,
  `rademacherTraceProbability_eventProb_vecNorm2_signedHadamard_le_mean_add_ge_one_sub_exp_m_t_sq_div_eight`,
  `rademacherTraceProbability_eventProb_forall_vecNorm2_signedHadamard_le_sqrt_add_ge_one_sub_m_exp_m_t_sq_div_eight`, and
  `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_sqrt_add_sq_ge_one_sub_m_exp_m_t_sq_div_eight`;
- the source-sharp leverage cap is closed by
  `rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_sqrt_add_sq_div_nat_ge_one_sub_m_exp_m_t_sq_div_eight`
  and
  `rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_sqrt_add_sq_div_nat_ge_one_sub_delta`;
- the scalar logarithmic budget algebra and the resulting all-row row-norm and
  leverage-probability wrappers are closed by
  `real_sqrt_eight_log_div_pos_of_pos_lt`,
  `real_mul_exp_neg_mul_sqrt_eight_log_div_sq_div_eight_eq`,
  `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_log_delta_ge_one_sub_delta`, and
  `rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_log_delta_ge_one_sub_delta`;
- the signed-Hadamard high-probability event has been composed with the uniform
  one-step Loewner bound in
  `rademacherTraceProbability_eventProb_forall_uniformRowOuterGramSample_signedHadamard_finiteLoewnerLe_ge_one_sub_delta`;
- the iid uniform-row product law, centered sample-average identity, one-step
  variance proxy, positive/negative trace-MGF bounds, and exact two-sided
  uniform sample-average concentration theorem are closed in
  `UniformRowSamplingMGF.lean`, ending with
  `uniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_tail_budget`.
- the signed-Hadamard preprocessing event and the iid uniform row-sampling
  event have been composed on the product law in
  `UniformRowSamplingComposition.lean`, ending with
  `signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta`.
- the source-sharp SRHT preprocessing event and the iid uniform row-sampling
  event have also been composed on the product law in
  `UniformRowSamplingComposition.lean`, ending with
  `signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht`;
- the logarithmic-preprocessing wrapper for that exact product-law theorem is
  closed by
  `signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess`.
- the floating-point uniform row-sketch transfer for the scoped
  coordinate-Hoeffding route is closed in `UniformRowSamplingFP.lean`, ending
  with
  `signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta`.
- the deterministic-radius refinement of that FP transfer is closed in
  `UniformRowSamplingFP.lean`: row-norm caps bound the sample-dependent budget
  by `uniformRowSampleGramFullFpConstBudget`, and
  `signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget`
  gives the fixed-radius high-probability event whenever a scalar `τ`
  dominates the sample-dependent budget over all joint outcomes.
- the source-sharp SRHT floating-point constant-budget transfer is closed in
  `UniformRowSamplingFP.lean` without a global domination hypothesis:
  `signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht`
  derives the fixed budget `uniformRowSampleGramFullFpConstBudget fp s (m*S^2)`
  on the same SRHT row-norm event, and
  `signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht_log_preprocess`
  supplies the logarithmic-preprocessing wrapper.

Remaining dependencies:

- broader Gaussian, FJLT, and input-sparsity uniformization routes remain
  separate theorem families, not blockers for the SRHT branch.

Rejected or insufficient routes:

- expectation alone is insufficient for a high-probability source theorem;
- the closed Markov/union theorem is useful but too weak to be Tropp Lemma 3.3;
- the closed coordinate-Hoeffding row-norm and leverage-probability theorems
  are real high-probability scoped routes, but they remain a weaker alternative
  now that the SRHT row-norm branch is closed in explicit-`t` form;
- a theorem that assumes the row-norm event or assumes concentration cannot
  close A3.4;
- a statement about the deterministic preprocessing products alone does not
  close the distribution-specific random projection claim.

Next admissible progress: this SRHT bottleneck is closed.  If Algorithm 3
non-SRHT distributions are brought into scope, create separate bottleneck rows
for Gaussian/FJLT/input-sparsity uniformization rather than reopening this SRHT
row.

## Active Red Bottlenecks

### `LS.8-rectangular-QR`

`LS.8-rectangular-QR` is active. The previous red bottleneck `A1.5-B1` is
closed for the cited square source-aligned theorem. The current red bottleneck
is the concrete rectangular Householder QR/preconditioner route for equation
(8): the library now has supplied-transform, strong common-panel, and
source-faithful columnwise panel contracts.  The active source route is now the
columnwise Householder QR analysis, because Higham's proof permits the
perturbation matrix to depend on the matrix column.  The compact rounded
dot/scale/subtract vector primitive is now closed with an explicit deterministic
budget and a visible budget-domination adapter into `HouseholderAppError`.
The route-source checkpoint chose the positive Higham columnwise route.  The
final stored QR factorization assembly is now closed by
`fl_householderStoredTrailingPanel_higham_columnwise_factorization`: it combines
the stored trailing columnwise perturbation sequence with the stored
`[R;0]`/top-RHS/upper-triangular shape facts for the same concrete loop.  The
red bottleneck is therefore narrowed past the factorization assembly and into
the solver/preconditioner handoff: the remaining work is to discharge, justify,
or keep visible the nonzero-diagonal, conditioning/inverse-budget, and
compact-smallness/product-budget obligations needed for triangular solves and
equation (8) preconditioner accuracy.  The nonzero-diagonal and inverse-budget
subroutes now have several visible-domain closures: local determinant/rank
witnesses replace raw inverse witnesses;
triangular-principal-minor wrappers derive determinant facts from visible
triangular shape plus nonzero local diagonal entries; condition-number and
diagonal-dominant wrappers remove increasingly abstract inverse-budget
hypotheses; the Cox--Higham raw-stage active-block mass field is now connected
to the same rank/determinant infrastructure by
`householderActiveBlockNorm2Sq_pos_sequence_of_leading_block_det_ne_zero`;
and the latest concrete-dual branch states compact smallness in
the product form `2D_k * (m * budget_k^2) < 1`.  These are still not a
source-faithful proof for generic full-column-rank QR.  The active remaining
dependencies are to supply the determinant/lower-zero fields for the chosen
concrete rounded loop, derive local diagonal dominance and product compact
smallness from a stronger computed-loop/conditioning invariant, to rule out a
listed route with evidence, or to make a route choice that keeps those
assumptions visibly as source/domain hypotheses.

Recent route-elimination progress: the positivity-only route for product
compact smallness is now ruled out locally.  The theorem
`not_forall_pos_implies_two_mul_mul_sq_lt_one` gives the scalar counterexample
`D = 1`, `B = 1`, `m = 1`, so `D > 0` alone cannot imply
`2D * (m * B^2) < 1`.  This closure has two clean weak-component passes.
The remaining positive route must supply a real compact-update budget bound
from a computed-loop/conditioning invariant, or the product-smallness
assumption must remain visible.

Further product-smallness route-elimination progress: local diagonal dominance
and the displayed Higham inverse budget also do not imply product compact
smallness by themselves.  The theorem
`not_forall_diagDominantUpper_implies_two_mul_budget_expr_mul_sq_lt_one`
instantiates the scalar `1 x 1` identity block, for which
`IsDiagDominantUpper 1 U` holds and the diagonal-dominant inverse budget is
positive, but the product condition with `B = 1` and `m = 1` asserts
`2 < 1`.  This has two clean weak-component passes.  The remaining positive
route must still derive the compact-update product inequality from a genuine
computed-loop or conditioning invariant, or keep it visibly as a domain
assumption.

Conditioning-facing product-smallness route elimination: upper-triangular
nonsingularity plus a finite local `κ∞` budget also does not imply product
compact smallness.  The theorem
`not_forall_upper_tri_det_ne_zero_kappaInf_bound_implies_two_mul_budget_expr_mul_sq_lt_one`
uses the same nonsingular triangular block `[[1,2],[0,1]]`, chooses the
conditioning budget to be its own formal `κ∞`, and takes compact budget
`B = 1`, so the product inequality fails.  Two weak-component passes validated
the targeted/full Lean builds, executable lookup, touched placeholder scan,
axiom audit, PDF text extraction, and rendered PDF pages 125--126.  This rules
out treating a finite condition-number certificate as an implicit
compact-update budget bound.

Current route-choice checkpoint: after the finite-conditioning/product-smallness
elimination, the remaining `LS.8-rectangular-QR` bottleneck is no longer a
missing adapter.  The local library has ruled out the easy shortcut routes from
whole-matrix nonsingularity/full rank, positive trailing norm, diagonal
dominance alone, product smallness alone, finite local `κ∞`, and mutual
implication between diagonal dominance and product smallness.  The next step
must choose one of three theorem families before more Lean proof work counts as
progress:

1. prove a new computed-loop/off-diagonal-control invariant that supplies both
   local diagonal dominance and the stored-sequence compact-product inequality;
2. switch from the unpivoted Higham columnwise QR route to a Cox--Higham style
   pivoted/sorted row-wise weighted least-squares theorem family, changing the
   algorithmic hypotheses;
3. keep local leading-block nonsingularity/nonzero diagonal, diagonal
   dominance, conditioning/inverse-budget, and compact-product smallness as
   visible domain hypotheses and mark the generic implementation-backed
   equation (8) QR/preconditioner theorem open.

Adjacent adapters, extra PDF prose, and new wrappers are frozen unless they
close one of these listed dependencies, rule out one of these routes with
evidence, or correct the theorem statement.

Cross-route route-elimination progress: product compact smallness also does
not imply diagonal dominance.  The theorem
`not_forall_upper_tri_det_ne_zero_product_budget_implies_diagDominant` uses
the nonsingular upper-triangular block `[[1,2],[0,1]]` and chooses
`B = 1/8`, so the displayed product-smallness inequality holds while
`IsDiagDominantUpper` fails.  Two weak-component passes validated the Lean
fact, lookup reference, axiom audit, PDF text extraction, and rendered PDF
pages 124--125.  This rules out collapsing the two remaining visible
assumptions into one another; both need a genuine invariant or must remain
domain assumptions.

Row-max/product-smallness route-elimination progress: product compact smallness
also does not imply the nonpositive row-max scalar defect.  The theorem
`not_forall_upper_tri_det_ne_zero_product_budget_implies_rowMaxDiagDefectBudget_nonpos`
uses the active-pivot row-budget counterexample sequence with compact budget
`B = 1/16`.  The displayed leading blocks are upper triangular and
nonsingular, and the product compact-smallness inequality holds, but at
displayed stage one the strict-upper row maximum is `2` while the displayed
diagonal magnitude is `1`.  This rules out using compact-product smallness as
a hidden substitute for row-max/off-diagonal control; a stronger concrete
pivoted/sorted/off-diagonal-control invariant must prove the row-max defect,
or the row-max assumption must remain visible.

Product-smallness/active-budget row-max route-elimination progress: adding the
active-pivot budget surface to product compact smallness still does not imply
the nonpositive row-max scalar defect.  The theorem
`not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_rowMaxDiagDefectBudget_nonpos`
uses the same active-pivot row-budget sequence with compact budget `B = 1/16`.
Upper-triangular nonsingular displayed leading blocks, positive active-block
mass, active max-pivoting, active/off-diagonal budget control, and the
compact-product inequality all hold, but the displayed row-max defect remains
positive at stage one.  Thus neither product smallness alone nor product
smallness plus the active-budget surface closes the row-max dependency.

Stage-diagonal/product-smallness route-elimination progress: product compact
smallness also does not imply the scalar stage-diagonal lower-bound condition.
The theorem
`not_forall_upper_tri_det_ne_zero_product_budget_implies_stageDiagLowerDefectBudget_nonpos`
uses the same active-pivot sequence with compact budget `B = 1/16` and fixed
stage budget `2`.  The product compact-smallness inequality holds, but the
stage-one displayed diagonal magnitude is only `1`, so the scalar
stage-diagonal defect is positive.  Compact-product smallness therefore cannot
replace the diagonal lower-bound invariant left by the active/prefix route.

Product-smallness/active-budget stage-diagonal route-elimination progress:
adding the active-pivot budget surface to product compact smallness still does
not imply the scalar stage-diagonal lower-bound condition.  The theorem
`not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageDiagLowerDefectBudget_nonpos`
uses compact budget `B = 1/16` and constant stage budget `2` on the same
active-pivot row-budget witness.  The active/pivot/budget and product
hypotheses hold, but the stage-one displayed diagonal magnitude is only `1`,
so the scalar stage-diagonal defect remains positive.

Active-pivot budget stage-diagonal route-elimination progress: the active-pivot
budget surface alone also cannot imply the scalar stage-diagonal condition.
The theorem
`not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageDiagLowerDefectBudget_nonpos`
is a small consequence of the product-plus-active obstruction: a universal
active-only implication would immediately yield the already-refuted
product-plus-active implication.  Thus active max-pivoting and
active/off-diagonal budget control are still not enough to close the scalar
stage-diagonal dependency.

Finite stage-diagonal packaging progress: the theorem
`storedQRStageDiagLowerDefectBudget_nonpos_of_stageBudget_le_diag` proves the
converse of the scalar extractor.  If the displayed pointwise diagonal
lower-bound family `stageBudget k <= |(S_k)_{ii}|` holds for every off-diagonal
row `i < k`, then the finite scalar defect
`storedQRStageDiagLowerDefectBudget hmn A_hat stageBudget` is nonpositive.
Together with `storedQRStageBudget_le_diag_of_stageDiagLowerDefectBudget_nonpos`,
this closes the finite-family packaging direction for the active/prefix
stage-diagonal route.  It does not prove the displayed diagonal lower-bound
family from a concrete pivoted/sorted/off-diagonal-controlled loop.

Finite stage-budget/row-max comparison packaging progress: the definition
`storedQRStageRowMaxComparisonDefectBudget` and its extractor/converse theorems
package the remaining displayed comparison `stageBudget k <= rowMax(k,i)` as
one finite scalar condition.  Nonpositivity of this scalar supplies the
displayed comparison family, and a pointwise comparison proof conversely
supplies scalar nonpositivity.  The scalar bridge
`storedQRStageDiagLowerDefectBudget_nonpos_of_rowMaxDiagDefectBudget_nonpos_stageRowMaxComparisonDefectBudget_nonpos`
now derives the scalar stage-diagonal condition from the two scalar row-max
dependencies: nonpositive row-max defect plus nonpositive comparison defect.
This closes only finite-family packaging of the comparison dependency; the
comparison still must come from a concrete pivoted/sorted/off-diagonal-control
invariant or remain visible.

Scalar-comparison active-pivot row-max surface progress: the active-pivot
row-max source-control, local solver, and probability equation (8) wrappers now
consume `storedQRStageRowMaxComparisonDefectBudget <= 0` directly instead of
the displayed pointwise comparison family.  The new wrappers use
`storedQRStageBudget_le_rowMax_of_stageRowMaxComparisonDefectBudget_nonpos`
to recover the old comparison and then reuse the visible row-max theorems.
This is a strict theorem-surface reduction for the listed comparison
dependency: the remaining red items are now the scalar row-max defect, the
scalar comparison defect, determinant/nonbreakdown or conditioning fields, and
global compact-product smallness.

Scalar-comparison route-elimination progress: the scalar finite comparison
defect is not forced by the current active-pivot active/off-diagonal budget
surface, even if product compact-smallness is added.  The theorems
`not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`
and
`not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`
use the finite-max extractor to reduce any attempted scalar proof to the
already-refuted displayed comparison route.  Thus the comparison defect must
come from a genuinely stronger pivoted/sorted/off-diagonal-control invariant
or remain visible.

Row-max-granted scalar-comparison route-elimination progress: even granting the
nonpositive scalar row-max defect does not make the scalar comparison defect a
consequence of the active-pivot active/off-diagonal budget surface.  The
diagonally safe witness
`activeMaxPivotRowMaxComparisonCounterexampleSeq` has
`storedQRRowMaxDiagDefectBudget <= 0`, but with uniform stage budget `3` it has
positive `storedQRStageRowMaxComparisonDefectBudget` because the displayed
stage-one strict-upper row maximum is `2`.  The theorems
`not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_rowMaxDiagDefect_implies_stageRowMaxComparisonDefectBudget_nonpos`
and
`not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_rowMaxDiagDefect_implies_stageRowMaxComparisonDefectBudget_nonpos`
therefore rule out this stronger shortcut, with or without product
compact-smallness.  The comparison scalar must be proved by a stronger
concrete loop invariant or remain visible.

Row-max-alone stage-diagonal route-elimination progress: the nonpositive
scalar row-max defect by itself also does not imply the downstream scalar
stage-diagonal condition.  The diagonally safe witness
`activeMaxPivotRowMaxComparisonCounterexampleSeq` still has
`storedQRRowMaxDiagDefectBudget <= 0`, but if the uniform stage budget is `4`
then the displayed stage-one diagonal defect is positive.  The theorem
`not_forall_rowMaxDiagDefectBudget_implies_stageDiagLowerDefectBudget_nonpos`
therefore rules out replacing the scalar comparison field by the row-max
defect alone.  The row-max bridge still needs the explicit comparison scalar,
a pointwise stage-budget/row-max comparison, or an equivalent stronger
concrete loop invariant.

Product/active row-max-granted stage-diagonal route-elimination progress:
even after adding active max-pivoting, active/off-diagonal budget control, and
compact-product smallness, the granted row-max scalar defect does not imply the
stage-diagonal scalar condition.  `LSQRSolve.lean` now proves
`not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_rowMaxDiagDefect_implies_stageDiagLowerDefectBudget_nonpos`
and
`not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_rowMaxDiagDefect_implies_stageDiagLowerDefectBudget_nonpos`.
The same diagonally safe witness uses stage budget `4` and compact budget
`B = 1/16`; the scalar stage-diagonal defect remains positive.  The comparison
scalar, pointwise comparison, or stronger concrete loop invariant remains a
real dependency.

Stage-budget/row-max product-smallness route-elimination progress: product
compact smallness also does not rescue the active-pivot comparison shortcut.
The theorem
`not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageBudget_le_rowMax`
adds product compact-smallness to the active max-pivot, active-block budget,
and displayed strict-upper budget hypotheses from the earlier comparison
counterexample.  With compact budget `B = 1/16` and uniform stage budget `3`,
all those hypotheses hold, but the displayed row maximum at stage one is `2`.
Thus the `stageBudget <= rowMax` comparison remains an independent invariant.

Computed-loop compact-budget progress: the product compact-smallness side now
has a stored-sequence bridge.  The theorem
`storedQRCompactPivotBudget_le_sequence_column_norm` proves that the raw pivot
compact component is bounded by the deterministic
`storedQRCompactSequenceRelativeBudget` times the current pivot-column norm.
The scalar monotonicity lemma `two_mul_mul_sq_lt_one_of_nonneg_le` transfers
product smallness from that larger sequence-column budget to the raw local
budget, and the solver wrapper
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualProductSequenceBudget`
uses this to feed the concrete-dual product certificate.  Two weak-component
passes validated the targeted and full Lean builds, executable lookup, touched
placeholder scan, axiom audit, PDF text extraction, and rendered PDF page 124.
This closes the direct raw-component dependency, but it still leaves the
sequence-column product inequality and local diagonal dominance as visible
assumptions unless a stronger invariant proves them.

Proof-source route-choice checkpoint: the external route already recorded in
the proof-source ledger remains the correct source chain for concrete
rectangular QR.  Higham's QR notes, Section 4.1, Theorem 4.5, give the
standard columnwise Householder backward-error theorem with one theoretical
orthogonal factor and column-dependent perturbation matrices.  Cox--Higham,
"Stability of Householder QR Factorization for Weighted Least Squares
Problems", Theorem 1.1 and Section 2, explain that stronger row-wise weighted
least-squares stability is not generic for unpivoted Householder QR and needs
pivoting/sorting/sign-choice hypotheses.  Therefore the next positive theorem
must choose one of three routes: continue the columnwise Higham Theorem 4.5
assembly, switch to the Cox--Higham row-wise pivoted/sorted theorem family, or
keep the remaining nonbreakdown/conditioning/product-smallness hypotheses
visible as domain assumptions.  Re-entering the diagonal-dominance shortcut is
not allowed unless a new theorem supplies an actual compact-update budget.

Cox--Higham route-scope correction: the pivoted/sorted row-wise weighted
least-squares route is not a drop-in closure for the current unpivoted
stored-QR theorem.  Higham's QR notes separate the standard columnwise
Householder theorem (Section 4.1, Theorem 4.5) from the row-wise weighted-LS
question and state that, in general, the row-wise answer is negative unless
column pivoting is combined with row pivoting or row sorting and the correct
sign choice.  Cox--Higham make the same distinction explicit: unpivoted
Householder QR can have unsatisfactory row-wise backward stability, and their
row-wise theorem is built around column pivoting plus row pivoting or row
sorting and a specified Householder sign convention.  Therefore route 2 is
deferred as a separate theorem family, not a way to close the current
unpivoted implementation-backed equation (8) solver/preconditioner theorem.
The remaining valid choices for the current theorem are to prove a stronger
computed-loop/off-diagonal-control invariant or to keep the remaining local
nonbreakdown, conditioning, diagonal-dominance, and product-smallness
hypotheses visible as domain assumptions.

Exact-QR-shape route-elimination progress: final exact QR structure still does
not supply diagonal dominance.  The Lean theorem
`not_forall_orthogonal_upper_factorization_implies_diagDominant` uses the
same upper-triangular block `[[1,2],[0,1]]` and the exact factorization
`A = I * R`, with `I` orthogonal and `R` upper triangular with nonzero
diagonal, to show that an orthogonal-times-upper factorization is not enough
to justify `IsDiagDominantUpper`.  This rules out a weaker version of route 1:
the remaining positive route cannot rely on the final QR shape alone; it must
derive a genuine off-diagonal-control invariant from the computed loop, or
keep diagonal dominance visible as a domain hypothesis.

Exact-no-pivot-Householder route-elimination progress: diagonal dominance is
not a generic consequence of the exact trailing Householder recurrence either.
The Lean theorem
`not_forall_exact_trailing_householder_sequence_implies_diagDominant` uses a
two-step source-style no-pivot Householder sequence with valid signed
Householder squared norms and nonzero denominators.  Starting from
`[[1,2],[0,1]]`, the sequence reaches `[[-1,-2],[0,-1]]`, so the final
triangular factor still violates `IsDiagDominantUpper`.  This rules out the
remaining shortcut version of route 1: any positive unpivoted theorem must
prove a separate off-diagonal-control invariant that is stronger than the
standard exact Householder recurrence, or keep diagonal dominance as a visible
domain assumption.

Route-choice state after exact-recurrence elimination: the current unpivoted
equation (8) QR/preconditioner theorem is no longer blocked by a missing local
adapter.  The false generic routes have been ruled out from full rank,
positive trailing norm, finite local conditioning, diagonal dominance/product
smallness alone, final exact QR shape, and the standard exact no-pivot
Householder recurrence.  The next admissible progress is therefore a theorem
scope choice: either add and prove a genuinely stronger computed-loop
off-diagonal-control invariant, change to a pivoted/sorted row-wise theorem
family, or keep the remaining nonbreakdown, conditioning, diagonal-dominance,
and compact-product assumptions visible as domain hypotheses.  Continuing on
the unpivoted theorem without one of these choices would only create adjacent
infrastructure and is frozen by the red-bottleneck rule.

Source-faithful budget-instantiation progress: the leading-dual route now has
two explicit least-squares QR wrappers,
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leading_dual_norm_budget`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leading_dual_norm_budget`.
They choose the repository final Gram/RHS radii and the stored compact-update
sequence budget inside the source-faithful prefix-span plus leading-dual
certificate.  This reduces the listed budget-instantiation dependency; it
does not construct the leading dual, derive prefix-span, or prove the dual
compact-smallness inequality.  The closure has two clean weak-component
passes.

Local-dual construction progress on the same source-faithful route: the
left-inverse row-norm branch now has explicit repository-budget wrappers,
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget`.
They construct the leading dual from a local leading-block left inverse, choose
the repository final budgets, and choose the stored compact-update sequence
budget.  This closes the local-dual-construction plus budget-instantiation
dependency under visible local left-inverse row-norm and compact-smallness
hypotheses.  The closure has two clean weak-component passes.  The remaining
positive route must derive prefix-span, local left inverses, row-norm budgets,
and compact-smallness from a computed-loop/conditioning invariant, or keep
those assumptions visibly classified as domain assumptions.

Norm-budget instantiation progress on that source-faithful local-inverse
route: the Frobenius and infinity branches now also have explicit repository
budget wrappers.  The new theorems reduce `||C_k||_F^2 <= K_k` and
`(k+1)||C_k||∞^2 <= K_k` to the local row route, then choose the repository
final Gram/RHS budgets and stored compact-update sequence budget.  This closes
the Frobenius/infinity norm-budget instantiation dependency under visible
prefix-span, local left-inverse, sign-choice, and compact-smallness
hypotheses.  The closure has two clean weak-component passes.  The remaining
positive route must derive prefix-span, local left inverses, inverse-norm
budgets, sign-choice/nonbreakdown, and compact-smallness from a
computed-loop/conditioning invariant, or keep those assumptions visibly
classified as domain assumptions.

Stored-prefix-span progress on the same source-faithful local-inverse route:
the QR layer now derives `qrPrefixSupportSpannedByPreviousColumns` from the
actual stored panel recurrence plus a local left inverse of each previous
transposed leading block.  The new least-squares wrapper
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_norm_budget`
uses that derived prefix-span fact in the row-norm compact-budget certificate.
This closes the separate prefix-span assumption for the row branch under
visible previous/current local left inverses.  Two clean weak-component passes
have passed: targeted/full builds, lookup, touched-file placeholder scans,
whitespace checks, repeated axiom audits, PDF compile/text extraction, and
rendered page inspection.  The remaining positive route must derive the local
left inverses, inverse-norm budgets, sign-choice/nonbreakdown, and
compact-smallness from a computed-loop/conditioning invariant, or keep those
assumptions visibly classified as domain assumptions.

Stored-prefix-span norm-budget progress: the Frobenius and infinity branches
now have the same source-faithful prefix-span derivation through
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_frobNorm_budget`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_infNorm_budget`.
This closes the separate prefix-span assumption for the repository-budgeted
Frobenius/infinity inverse-norm branches under visible previous/current local
left inverses.  Two clean weak-component passes passed.  The remaining
positive route must derive the local left inverses, inverse Frobenius/infinity
budgets, sign-choice/nonbreakdown, and compact-smallness from a computed-loop
or conditioning invariant, or keep those assumptions visible.

Signed-alpha row progress on the same source-faithful stored-prefix-span route:
the row-norm local-inverse certificate now consumes the repository
`signedHouseholderAlpha` definition directly through
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_norm_budget`.
The wrapper derives the squared-alpha trailing-norm identity and nonpositive
pivot product internally, then reuses the stored-prefix-span row certificate.
Two clean weak-component passes passed: targeted/full builds, lookup,
touched-file placeholder scan, whitespace check, repeated axiom audit, PDF
compile/text extraction, and rendered page inspection.  The remaining positive
route must derive the local left inverses, row-norm budget, and compact
smallness from a computed-loop or conditioning invariant, extend the same
signed-alpha removal to the Frobenius/infinity branches, or keep the remaining
assumptions visible.

Signed-alpha inverse-norm progress on the same source-faithful stored-prefix-span
route: the Frobenius and infinity local-inverse certificates now consume
`signedHouseholderAlpha` directly through
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_frobNorm_budget`
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_infNorm_budget`.
The wrappers derive the squared-alpha identity and nonpositive pivot product
internally, then reuse the stored-prefix-span Frobenius/infinity certificates.
Two clean weak-component passes passed: targeted/full builds, lookup,
touched-file placeholder scan, whitespace check, repeated axiom audit, PDF
compile/text extraction, and rendered page inspection.  The remaining positive
route must derive the local left inverses, inverse-norm budgets, and compact
smallness from a computed-loop or conditioning invariant, or keep those
assumptions visible.

Determinant local-inverse progress on the same source-faithful signed-alpha
stored-prefix-span route: the row, Frobenius, and infinity certificates now
instantiate the previous/current local left-inverse witnesses with
`nonsingInv` from nonzero determinants of the previous transposed leading block
and the current leading block through
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_norm_budget`,
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_frobNorm_budget`,
and
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_infNorm_budget`.
Two clean weak-component passes passed: targeted/full builds, lookup,
touched-file placeholder scan, whitespace check, repeated axiom audit, PDF
compile/text extraction, and rendered page inspection.  The remaining positive
route must derive the determinant facts, row/Frobenius/infinity inverse-budget
inequality, and compact-smallness from a computed-loop or conditioning
invariant, or keep those assumptions visible.

Condition-number budget progress on the same determinant route: the infinity
certificate now has a `κ∞` self-norm companion,
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_budget`.
It derives the direct inverse-∞ budget from the existing local
`infNorm_sq_budget_of_kappaInf_le_and_det_ne_zero` bridge, so the direct
inverse-budget dependency is reduced to visible determinant, local `κ∞`, and
self-norm budget hypotheses.  Two clean weak-component passes passed:
targeted/full builds, lookup, touched-file placeholder scan, whitespace check,
repeated axiom audit, PDF compile/page-local text extraction, and rendered page
inspection.  The remaining positive route must derive determinant facts,
conditioning budgets, and compact-smallness from a computed-loop invariant, or
keep those assumptions visible.

Triangular determinant progress on the same source-faithful signed-alpha
condition-number route: the theorem
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_upperTriangular_leadingDiag_ne_zero_kappaInf_selfNorm_budget`
derives the previous/current determinant facts from visible upper-triangular
leading-block shape and nonzero displayed leading diagonal entries, then reuses
the signed-alpha determinant `κ∞` wrapper.  Two clean weak-component passes
passed: targeted/full builds, lookup, touched-file placeholder scan, whitespace
check, repeated axiom audit, PDF compile/page-local text extraction, and
rendered page inspection after repairing an inline Lean-name overflow in the
proof idea.  The remaining positive route must derive the triangular/nonzero
diagonal invariant, conditioning budgets, and compact-smallness from a
computed-loop invariant, or keep those assumptions visible.

Further route-elimination progress: the determinant-facing triangular
nonsingularity route for diagonal dominance is now ruled out locally.  The
theorems `diagDominanceCounterexample2_det_ne_zero` and
`not_forall_upper_tri_det_ne_zero_implies_diagDominant` show that even an
upper-triangular matrix with nonzero determinant need not satisfy the
repository's diagonal-dominance hypothesis.  This closure has two clean
weak-component passes.  The remaining positive route must derive diagonal
dominance from a stronger computed-loop/conditioning invariant, or diagonal
dominance must remain visible as a domain assumption.

Conditioning-facing route-elimination progress: the theorem
`exists_upper_tri_det_ne_zero_kappaInf_bound_not_diagDominant` and its
universal companion
`not_forall_upper_tri_det_ne_zero_kappaInf_bound_implies_diagDominant` show
that upper-triangular shape, nonsingularity, and a finite local `κ∞` budget do
not by themselves imply diagonal dominance.  The same matrix `[[1,2],[0,1]]`
is the witness, with the budget chosen to be its own `kappaInf` value.  This
rules out treating a generic finite condition-number certificate as the missing
diagonal-dominance invariant; a positive route must use a stronger invariant
that directly controls off-diagonal entries relative to pivots, or keep
diagonal dominance visible.

Latest source-shaped current-pivot reduction: the off-diagonal-control route
now replaces the raw current pivot nonzero condition by nonsingularity of the
displayed local leading block.  The new theorem
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_sqrtBudget_offdiag_product`
uses the existing stored lower-zero determinant bridge
`fl_householderStoredTrailingPanel_sequence_current_pivot_ne_zero_of_leadingBlock_det_ne_zero`
to derive `A_hat k k k != 0` from `det S_k != 0`, then reuses the signed-alpha
prefix-diagonal reduction.  Its solver-facing companion
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_sqrtBudget_offdiag_product`
feeds the reduced source-shaped data into `LSQRSolveBackwardError` with the
repository final Gram/RHS budgets.  This closes a listed current-pivot
dependency inside the red bottleneck; it does not prove local leading-block
nonsingularity, the square-root nonbreakdown budget, row-wise off-diagonal
domination, or compact-product smallness from the ordinary no-pivot loop.

Latest source-shaped budget-shape reduction: the square-root nonbreakdown
field in the same determinant-shaped route has now been replaced by the
dimensioned norm-square margin
`m * B_k^2 < ||A_hat_k(k:m,k)||_2^2`.  The theorem
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_offdiag_product`
uses the repository bridge
`budget_lt_sqrt_householderTrailingNorm2Sq_of_dim_mul_budget_sq_lt_trailingNorm2Sq`
and then reuses the determinant-shaped source theorem; the solver companion
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_offdiag_product`
feeds the result to the final QR certificate.  This closes a listed
budget-shape dependency; it does not prove the norm-square margin itself.
The remaining admissible progress is to prove local leading-block
nonsingularity, the norm-square nonbreakdown margin, row-wise off-diagonal
domination, and compact-product smallness from a pivoting, ordering, or
off-diagonal-growth assumption, change theorem family, or keep them visible as
domain hypotheses.

Route-1 row-max contraction progress: the positive computed-invariant handoff
is now explicit.  The theorem
`StoredQRDisplayedRowBudgetControl.of_rowMaxBudget_le_diag_factor` proves that
if a computed-loop invariant supplies one scalar `ρ <= 1` with
`qrLeadingStrictUpperRowMaxBudget <= ρ * |diag|` for every displayed row
`i < k`, then the canonical row-max budget satisfies
`StoredQRDisplayedRowBudgetControl`.  The source-control companion
`StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowMaxBudgetFactor_globalProduct`
and solver companion
`LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowMaxBudgetFactor_globalProduct`
compose that contraction certificate with the stored recurrence, determinant,
norm-square nonbreakdown, and scalar finite global compact-product fields.
Two weak-component validation passes are clean: repeated `git diff --check`,
touched source Lean marker scan, focused LSQRSolve build, executable lookup,
qualified axiom audit, PDF compile/text extraction, and rendered page inspection
passed.  This closes the row-budget-certificate construction under a genuine
route-1 invariant shape; it does not prove the contraction invariant,
determinant facts, norm-square margin, global product smallness, or the final
generic QR/preconditioner theorem from ordinary no-pivot QR.

Scalar route-1 defect progress: the row-max contraction check can now be
expressed as one finite scalar defect.  The definition
`storedQRRowMaxDiagDefectBudget` takes the maximum of
`rowMax - |diag|` over displayed strict-upper rows `i < k`; the theorem
`StoredQRDisplayedRowBudgetControl.of_rowMaxDiagDefectBudget_nonpos` proves
that a nonpositive scalar defect builds the packaged row-budget certificate.
The source-control and solver companions with suffix
`rowMaxDiagDefect_globalProduct` compose that certificate with the stored
recurrence, determinant, norm-square nonbreakdown, and scalar finite
global-product fields.  The first weak-component pass is clean, including
whitespace, touched-source marker scan, focused LSQRSolve build, executable
lookup, qualified axiom audit, PDF compile/text extraction, and rendered page
inspection of pages 176--178.  The second weak-component pass is also clean
with the same standard axiom audit result.  This checkpoint now has two
consecutive clean passes.  This is still only a dependency reduction:
it does not prove that a concrete no-pivot QR loop has nonpositive scalar
defect, nor determinant facts, norm-square margin, product smallness, or the
final generic QR/preconditioner theorem.

## Closed Red Bottleneck: A1.5-B1

**Source claim.** CACM Algorithm 1, equation (2): the elementwise sampler with
squared-magnitude probabilities should satisfy a high-probability
spectral-norm residual bound.

**Current status.** CLOSED for the cited square source-aligned theorem.  The
finite-dimensional Lieb/relative-entropy foundation and the one-step
Tropp trace-MGF inequality are now proved locally.  The Algorithm 1
product-law trace-MGF iteration and its finite-real trace-exponential adapter
are also proved locally, and the finite-real theorem is now instantiated with
the actual Algorithm 1 self-adjoint dilation residual.  The trace-exponential
Markov/eigenvalue interface is also specialized to that residual.  The
repository now proves both the scalar Bernstein parabola inequality with the
needed constants and the explicit CFC lift from a real-spectrum upper bound to
the operator quadratic inequality
\(\exp(\theta X)\preceq I+\theta X+g(\theta,R)X^2\).  It also proves the
generic centered one-sample matrix-CGF/log-MGF variance-proxy bound
\(\log\mathbb E\exp(\theta X)\preceq g(\theta,R)\mathbb E[X^2]\), including
support-aware variants.  That theorem is now instantiated with the truncated
Algorithm 1 self-adjoint dilation increments in
`sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`.
The one-sample C-star variance proxy, the positive and negative trace-MGF
scalarizations, and the two-sided trace-exponential Markov tail skeleton are
also proved locally.  A source-sharp square variant is now proved as well: it
uses the direct rectangular dilation support bound, the vector/transpose-vector
second-moment calculation, and the variance scale
\(V=n\|\widehat A\|_F^2/s^2\).  The source-sharp square scaled-radius and
Bennett-radius spectral-event corollaries are now closed as well.  The source
sample-complexity/final-constant simplification of that Bennett budget, final
truncation transfer to the CACM equation (2) constants, and the downstream
support-aware floating-point gamma-budget spectral transfer are also closed.
For the literal, untruncated rectangular law, the exact one-step dilation
variance proxy is now sharpened from the older Frobenius-detour scale
\(2mn\|A\|_F^2/s^2\) to
\(\max\{m,n\}\|A\|_F^2/s^2\), including real quadratic-form, Loewner, and
C-star expectation forms.  The independent `s`-sample product-law expectation
and trace adapters are also closed at scale
\(\max\{m,n\}\|A\|_F^2/s\).  This closes the rectangular variance-proxy
dependency, not the final matrix-Bernstein/Khintchine tail conversion.

**Exact blocking theorem family.**

1. Closed: Algorithm 1 instantiation of the now-generic one-sample
   matrix-CGF/log-MGF theorem for the truncated self-adjoint dilation residual
   increments:

   ```lean
   sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le
   ```

2. Closed: parameterized upper-tail and two-sided trace-MGF-to-eigenvalue
   Bernstein skeletons for the truncated Algorithm 1 dilation, including an
   explicit `1 - δ` form obtained by choosing `T = log (2B/δ)`:

   ```lean
   sqMagTraceProbability_eventProb_exists_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_ge_le_exp
   sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp
   real_exp_neg_log_two_mul_div_mul_self_add
   sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta
   ```

3. Closed: source-sharp square variance and two-sided tail skeletons:

   ```lean
   sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleResidualIncrement_le_sharp
   sqMagProb_sum_vecNorm2Sq_transposeRectMatMulVec_elementwiseSampleResidualIncrement_le_sharp
   sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_square
   sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_square
   sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_square
   sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_square
   sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_square
   sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp_sharp_square
   sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta_sharp_square
   ```

4. Closed: source-sharp square spectral conversion and Bennett optimization:

   ```lean
   sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius_sharp_square
   sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius_sharp_square
   ```

5. Closed: source-sharp denominator simplification, source sample budget,
   deterministic truncation transfer, and support-aware floating-point gamma
   budget:

   ```lean
   real_bennett_transform_lower_bound_two_add_two_thirds
   real_bennett_budget_of_quadratic_denominator_two_add_two_thirds
   elementwiseTruncate_tau_le_frobNormRect_of_sqMagProbDen_pos
   sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_source_sample_budget_sharp_square
   sqMagTraceProbability_eventProb_algorithm1ExactTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_square
   fl_elementwiseTraceSketch_zero_init_sqMag_error_bound_of_positiveProb
   sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_gamma_square
   ```

6. Closed: literal untruncated rectangular variance-proxy dependency:

   ```lean
   sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_rect
   sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect
   sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect
   sqMagProb_sum_steps_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_rect
   sqMagProb_sum_steps_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect
   sqMagProb_sum_finiteTrace_rectSelfAdjointDilation_square_le_sharp_rect
   sqMagProb_sum_steps_finiteTrace_rectSelfAdjointDilation_square_le_sharp_rect
   sqMagTraceProbability_expectationReal_finiteQuadraticForm_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect
   sqMagTraceProbability_expectationReal_sum_finiteQuadraticForm_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect
   sqMagTraceProbability_sum_expectationReal_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect
   ```

7. Closed route-elimination dependency for the literal untruncated support
   premise:

   ```lean
   algorithm1SmallEntrySupportMatrix
   sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos
   sqMagProb_algorithm1SmallEntrySupportMatrix_small_pos
   algorithm1SmallEntrySupportMatrix_residual_increment_abs_eq
   algorithm1SmallEntrySupportMatrix_residual_increment_not_rectOpNorm2Le
   exists_sqMagPositive_sampleResidualIncrement_entry_abs_gt
   exists_sqMagPositive_sampleResidualIncrement_not_rectOpNorm2Le
   sqMagTraceProbability_eventProb_not_algorithm1ExactSpectralEvent_smallEntry_pos
   ```

   These theorems prove that, for every proposed scalar radius, a
   positive-probability small-entry sample under the exact literal
   squared-magnitude law violates the rectangular operator-norm support
   predicate, and that the one-step exact product law assigns strictly
   positive probability to the bad exact spectral-radius event.  Therefore the
   current support-aware Bernstein API cannot close the source-uniform
   literal equation (2) theorem by a uniform deterministic bounded-increment
   radius.

The exact Lean names may change as the theorem shapes are refined, but they
do not assume the desired concentration event, Algorithm 1 CGF instantiation,
or matrix Bernstein theorem as hypotheses.

## Dependencies

Closed dependencies:

- `strictPositiveCStarMatrixCone`
- `mem_strictPositiveCStarMatrixCone`
- `cstarMatrix_isStrictlyPositive_pos_real_smul`
- `cstarMatrix_nonneg_nonneg_real_smul`
- `cstarMatrix_isStrictlyPositive_pos_nonneg_real_smul_add`
- `strictPositiveCStarMatrixCone_convex`
- `cstarMatrix_log_isSelfAdjoint`
- `liebTraceArgument_isSelfAdjoint`
- `liebTraceArgument_isStarNormal`
- `cstarMatrixTrace_im_eq_zero_of_isSelfAdjoint`
- `liebTraceCfcExp_nonneg`
- `liebTraceFunctional_trace_im_eq_zero`
- `liebTraceFunctional`
- `liebTraceFunctional_nonneg`
- `liebTraceFunctional_eq_normedSpace_exp`
- `liebTraceFunctional_zero_eq_trace`
- `liebTraceConcavityTarget`
- `liebTraceConcavityTarget_zero`
- `cstarMatrixRelativeEntropyPerspectiveTraceRepresentation_all`
- `cstarMatrixRelativeEntropyJointConvexOnStrictPositive_all`
- `liebTraceConcavityTarget_all`
- `FiniteProbability.exists_prob_pos`
- `FiniteProbability.expectationCStarMatrix_isStrictlyPositive`
- `cstarMatrix_normedSpace_exp_isStrictlyPositive_of_isSelfAdjoint`
- `cstarMatrix_cfc_complex_exp_isStrictlyPositive_of_isSelfAdjoint`
- `cstarMatrix_cfc_real_exp_isStrictlyPositive_of_isSelfAdjoint`
- `liebTraceCfcExp_isStrictlyPositive`
- `FiniteProbability.expectationReal_trace_normed_exp_add_le_of_liebTraceConcavityTarget`
- `FiniteProbability.expectationReal_trace_normed_exp_add_le`
- `sqMagSampleProbability`
- `sqMagTraceProbability_expectationComplex_step_eq`
- `sqMagTraceProbability_expectationCStarMatrix_step_eq`
- `sqMagTraceProbability_expectationCStarMatrix_step_eq_sampleExpectation`
- `sqMagTraceProbability_expectationReal_trace_normed_exp_add_step_le`
- `sqMagTraceProbMass_snoc`
- `sqMagTraceProbability_expectationReal_succ_last_eq`
- `sqMagTraceProbability_expectationReal_trace_normed_exp_add_sum_le`
- `finiteComplexCStarMatrix_zero`
- `finiteComplexCStarMatrix_add`
- `finiteComplexCStarMatrix_finset_sum`
- `finiteComplexCStarMatrixRingHom`
- `finiteComplexCStarMatrixRingHom_continuous`
- `finiteComplexCStarMatrix_finiteMatrixExp`
- `cstarMatrixTrace_normed_exp_finiteComplexCStarMatrix`
- `cstarMatrixTrace_normed_exp_finiteComplexCStarMatrix_re`
- `sqMagTraceProbabilityFiniteRealTraceMGFLogBound`
- `sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le`
- `rectSelfAdjointDilation_elementwiseSampleResidualIncrement_smul_symmetric`
- `sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_sum_rectSelfAdjointDilation_sampleResidualIncrement_le`
- `sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_rectSelfAdjointDilation_elementwiseTraceResidual_le`
- `sqMagTraceProbability_eventProb_exists_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_ge_le`
- `sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_lt_ge`
- `sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le`
- `sqMagSampleProbability_neg_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le`
- `sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`
- `sqMagTraceProbability_eventProb_exists_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_ge_le_exp`
- `sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`
- `sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp`
- `real_exp_neg_log_two_mul_div_mul_self_add`
- `sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta`
- `vecNorm2Sq_rectMatMulVec_elementwiseSampleContribution_eq`
- `sqMagProb_mul_elementwiseIncrement_sq_le`
- `sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleContribution_le`
- `sqMagProb_sum_rectMatMulVec_elementwiseSampleContribution_eq`
- `sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleResidualIncrement_le_sharp`
- `vecNorm2Sq_transposeRectMatMulVec_elementwiseSampleContribution_eq`
- `sqMagProb_sum_vecNorm2Sq_transposeRectMatMulVec_elementwiseSampleContribution_le`
- `sqMagProb_sum_transposeRectMatMulVec_elementwiseSampleContribution_eq`
- `sqMagProb_sum_vecNorm2Sq_transposeRectMatMulVec_elementwiseSampleResidualIncrement_le_sharp`
- `sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_square`
- `sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_square`
- `sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_square`
- `sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp`
- `sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_square`
- `sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_square`
- `sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp_sharp_square`
- `sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta_sharp_square`
- `real_exp_quadratic_remainder_monotone`
- `real_exp_sub_self_sub_one_nonneg`
- `real_sq_div_two_le_exp_sub_self_sub_one_of_nonneg`
- `real_exp_le_one_add_self_add_sq_div_two_of_nonpos`
- `real_exp_tail_two_hasSum`
- `real_exp_mul_le_quadratic_of_nonneg_of_nonneg_of_le_one`
- `real_exp_mul_le_quadratic_of_nonneg_of_le_one`
- `real_exp_mul_le_quadratic_scaled_of_nonneg_of_pos_of_le`
- `cstarMatrix_cfc_quadratic_eq`
- `cstarMatrix_cfc_real_exp_mul_le_quadratic_of_spectrum`
- `cstarMatrix_cfc_real_exp_mul_le_bernstein_quadratic_of_spectrum_le`
- `FiniteProbability.expectationCStarMatrix_real_smul`
- `FiniteProbability.expectationCStarMatrix_nonneg_of_prob_pos`
- `FiniteProbability.expectationCStarMatrix_mono_of_prob_pos`
- `cstarMatrix_spectrum_le_of_le_real_smul_one`
- `cstarMatrix_real_smul_isSelfAdjoint`
- `cstarMatrix_cfc_real_exp_mul_eq_normedSpace_exp_real_smul`
- `cstarMatrix_selfAdjoint_mul_self_nonneg`
- `cstarMatrix_one_add_le_normedSpace_exp_of_nonneg`
- `cstarMatrix_log_one_add_le_self_of_nonneg`
- `FiniteProbability.expectationCStarMatrix_cfc_real_exp_mul_le_bernstein_variance_proxy`
- `FiniteProbability.cstarMatrix_log_expectationCStarMatrix_cfc_real_exp_mul_le_bernstein_variance_proxy`
- `FiniteProbability.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy`
- `FiniteProbability.expectationCStarMatrix_cfc_real_exp_mul_le_bernstein_variance_proxy_of_prob_pos`
- `FiniteProbability.cstarMatrix_log_expectationCStarMatrix_cfc_real_exp_mul_le_bernstein_variance_proxy_of_prob_pos`
- `FiniteProbability.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy_of_prob_pos`
- `sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero`
- `sqMagSampleProbability_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le`
- `sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`
- `realRelativeEntropy`
- `realRelativeEntropy_self`
- `realRelativeEntropy_nonneg`
- `finiteRealRelativeEntropy`
- `finiteRealRelativeEntropy_self`
- `finiteRealRelativeEntropy_nonneg`
- `finite_log_sum_inequality`
- `realRelativeEntropy_jointConvex_of_pos_weights`
- `realRelativeEntropy_jointConvex`
- `finiteRealRelativeEntropy_jointConvex`
- `complex_realContinuousFunctionalCalculus`
- `piComplex_realContinuousFunctionalCalculus`
- `cstarMatrixDiagonalStarAlgHom`
- `cstarMatrixDiagonalStarAlgHom_continuous`
- `cstarMatrixRealDiagonal`
- `cstarMatrixRealDiagonal_smul_add`
- `cstarMatrixTrace_realDiagonal`
- `cstarMatrix_log_realDiagonal`
- `cstarMatrixRelativeEntropy`
- `cstarMatrixRelativeEntropy_self`
- `cstarMatrixRelativeEntropy_realDiagonal`
- `cstarMatrixRelativeEntropy_realDiagonal_nonneg`
- `positive_weighted_sum_pos`
- `cstarMatrixRelativeEntropy_realDiagonal_jointConvex`
- `cstarMatrixLeftMul`
- `cstarMatrixRightMul`
- `cstarMatrixLeftMul_mul`
- `cstarMatrixRightMul_mul`
- `cstarMatrixLeftMul_pow`
- `cstarMatrixRightMul_pow`
- `cstarMatrixLeftMul_real_smul_add`
- `cstarMatrixRightMul_real_smul_add`
- `cstarMatrixLeftRightMul_commute`
- `cstarMatrixLeftMul_isUnit_of_isStrictlyPositive`
- `cstarMatrixRightMul_isUnit_of_isStrictlyPositive`
- `cstarMatrixLeftRightRatio`
- `cstarMatrixLeftRightRatio_apply`
- `cstarMatrixLeftRightRatio_apply_unit`
- `cstarMatrixLeftRightRatio_apply_of_unit_eq`
- `cstarMatrixLeftRightRatio_apply_of_isStrictlyPositive`
- `matrix_kronecker_left_identity_real_smul_add`
- `matrix_kronecker_right_identity_real_smul_add`
- `matrix_kronecker_left_identity_mul_right_identity`
- `matrix_kronecker_right_identity_mul_left_identity`
- `matrix_kronecker_left_right_commute`
- `matrix_kronecker_posDef_left_identity`
- `matrix_kronecker_posDef_right_identity`
- `matrix_trace_kronecker`
- `matrix_trace_kronecker_left_identity`
- `matrix_trace_kronecker_right_identity`
- `cstarMatrixPositiveOperatorConvexTarget`
- `cstarMatrixPositiveOperatorConvexAllFiniteTarget`
- `cstarMatrixPositiveOperatorConvexTarget_id`
- `cstarMatrixPositiveOperatorConvexAllFiniteTarget_id`
- `cstarMatrixPositiveHansenPedersenTransferTarget`
- `cstarMatrixPositiveHansenPedersenTransferAllFiniteTarget`
- `cstarMatrixXLogXPositiveOperatorConvexTarget`
- `cstarMatrixXLogXHansenPedersenTransferTarget`
- `cstarMatrixXLogXPositiveOperatorConvexAllFiniteTarget`
- `cstarMatrixXLogXHansenPedersenTransferAllFiniteTarget`
- `cstarMatrixHansenPedersenJensenTwoPointTarget`
- `cstarMatrixHansenPedersenJensenTwoPointTarget_id`
- `cstarMatrixXLogXHansenPedersenJensenTarget`
- `cstarMatrixXLogXHansenPedersenJensenTarget_of_positiveOperatorConvex_of_transfer`
- `cstarMatrixXLogXHansenPedersenJensenTarget_of_transfer`
- `cstarMatrixXLogXPositiveOperatorConvexAllFiniteTarget_of_unit_interval_kernel`
- `cstarMatrixXLogXHansenPedersenJensenTarget_of_allFiniteTransfer`
- `cstarMatrixBlockDiagonal`
- `cstarMatrixBlockDiagonal_zero_zero`
- `cstarMatrixBlockDiagonal_one_one`
- `cstarMatrixBlockDiagonal_add`
- `cstarMatrixBlockDiagonal_neg`
- `cstarMatrixBlockDiagonal_sub`
- `cstarMatrixBlockDiagonal_star`
- `cstarMatrixBlockDiagonal_isSelfAdjoint`
- `cstarMatrixBlockDiagonal_mul`
- `cstarMatrixBlockDiagonal_isUnit`
- `cstarMatrixBlockDiagonal_left_nonneg`
- `cstarMatrixBlockDiagonal_right_nonneg`
- `cstarMatrixBlockDiagonal_nonneg`
- `cstarMatrixBlockDiagonal_isStrictlyPositive`
- `cstarMatrixBlockDiagonalStarAlgHom`
- `cstarMatrixBlockDiagonalStarAlgHom_apply`
- `cstarMatrixBlockDiagonalStarAlgHom_continuous`
- `cstarMatrixColumnPair`
- `cstarMatrixColumnPair_conjTranspose_mul_columnPair`
- `cstarMatrixColumnPair_conjTranspose_mul_self`
- `cstarMatrixBlockDiagonal_mul_columnPair`
- `cstarMatrixColumnPair_conjTranspose_mul_blockDiagonal_mul_columnPair`
- `cstarMatrixColumnPair_conjTranspose_mul_self_eq_one_of_sum`
- `cstarMatrix_mul_assoc_rect`
- `cstarMatrix_mul_add_rect`
- `cstarMatrix_add_mul_rect`
- `cstarMatrix_mul_smul_rect`
- `cstarMatrix_smul_mul_rect`
- `cstarMatrix_mul_one_rect`
- `cstarMatrix_one_mul_rect`
- `cstarMatrixColumnPairRangeProjection`
- `cstarMatrixColumnPairRangeProjection_isSelfAdjoint`
- `cstarMatrixColumnPairRangeProjection_mul_self_of_sum`
- `cstarMatrixColumnPairRangeProjection_mul_columnPair_of_sum`
- `cstarMatrixColumnPair_conjTranspose_mul_rangeProjection_of_sum`
- `cstarMatrixProjectionReflection`
- `cstarMatrixProjectionReflection_isSelfAdjoint_of_isSelfAdjoint`
- `cstarMatrixProjectionReflection_mul_self_of_idempotent`
- `cstarMatrixProjectionReflection_isUnit_of_idempotent`
- `cstarMatrixProjectionReflection_mem_unitary_of_isSelfAdjoint_of_idempotent`
- `cstarMatrixProjectionReflection_mul_of_mul_eq_self`
- `cstarMatrix_mul_projectionReflection_of_mul_eq_self`
- `cstarMatrix_reflectionAverage_compression_of_fixed`
- `cstarMatrix_reflectionAverage_conj_of_involutive`
- `cstarMatrix_reflectionAverage_commute_of_involutive`
- `cstarMatrix_commute_projection_of_commute_reflection`
- `cstarMatrixColumnPairRangeReflection`
- `cstarMatrixColumnPairRangeReflection_isSelfAdjoint`
- `cstarMatrixColumnPairRangeReflection_mul_self_of_sum`
- `cstarMatrixColumnPairRangeReflection_isUnit_of_sum`
- `cstarMatrixColumnPairRangeReflection_mem_unitary_of_sum`
- `cstarMatrixColumnPairRangeReflection_mul_columnPair_of_sum`
- `cstarMatrixColumnPair_conjTranspose_mul_rangeReflection_of_sum`
- `cstarMatrixColumnPair_reflectionAverage_compression_of_sum`
- `cstarMatrixColumnPair_reflectionAverage_conj_rangeReflection_of_sum`
- `cstarMatrixColumnPair_reflectionAverage_commute_rangeReflection_of_sum`
- `cstarMatrixColumnPair_reflectionAverage_commute_rangeProjection_of_sum`
- `cstarMatrixColumnPair_mul_columnPair_eq_columnPair_compression_of_commute`
- `cstarMatrixColumnPair_conjTranspose_mul_eq_compression_mul_conjTranspose_of_commute`
- `cstarMatrixColumnPair_reflectionAverage_mul_columnPair_of_sum`
- `cstarMatrixColumnPair_conjTranspose_mul_reflectionAverage_of_sum`
- `cstarMatrixBlockDiagonal_cfc`
- `cstarMatrix_cfc_unitary_conj`
- `cstarMatrix_compression_nonneg`
- `cstarMatrix_compression_mono`
- `cstarMatrixColumnPair_reflectionAverage_cfc_le_average_of_sum`
- `cstarMatrixColumnPair_reflectionAverage_compressed_cfc_le_compressed_of_sum`
- `cstarMatrix_unitary_conj_isStrictlyPositive`
- `cstarMatrixColumnPairRangeReflection_conj_isStrictlyPositive_of_sum`
- `cstarMatrix_isStrictlyPositive_of_matrix_posDef`
- `cstarMatrixColumnPair_mulVec_injective_of_sum`
- `cstarMatrixColumnPair_compress_blockDiagonal_isStrictlyPositive_of_sum`
- `cstarMatrixHansenPedersenCompression_isStrictlyPositive_of_sum`
- `cstarMatrix_cfc_one_add_log_eq_one_add_log`
- `cstarMatrix_spectrum_nonneg_of_nonneg`
- `cstarMatrix_cfc_one_sub_one_add_inv_monotone`
- `cstarMatrix_cfc_pos_over_one_add_monotone`
- `cstarMatrix_cfc_pos_over_pos_add_monotone`
- `cstarMatrix_cfc_unit_interval_fractional_kernel_monotone`
- `cstarMatrix_cfc_unit_interval_fractional_kernel_monotone_of_mem_Icc`
- `cstarMatrix_cfc_finset_sum_nonneg_mul_pos_over_pos_add_monotone`
- `cfc_integral_mono_of_forall_of_bound`
- `cstarMatrixXLogXDerivativeMonotoneTarget`
- `cstarMatrixXLogXDerivativeMonotoneTarget_of_log_monotone`
- `cstarMatrixStrictPositiveOperatorMonotoneTarget`
- `realXLogXDividedDifference`
- `realXLogXDividedDifference_self`
- `realXLogXDividedDifference_eq_log_add_ratio`
- `realXLogXDividedDifference_eq_log_add_normalized`
- `realNormalizedLogKernel`
- `realNormalizedLogKernel_eq_of_ne_one`
- `realNormalizedLogKernel_eq_mul_dslope_log`
- `continuousOn_realNormalizedLogKernel_Ioi`
- `realXLogXDividedDifference_eq_log_add_normalizedKernel`
- `real_normalizedLogKernel_offdiag_intervalIntegral`
- `realNormalizedLogKernel_setIntegral`
- `real_xlog_eq_sub_one_mul_realNormalizedLogKernel`
- `real_xlog_eq_sub_one_mul_normalizedKernel_setIntegral`
- `real_unit_interval_xlog_integrand_eq_affine_add_shifted_inv`
- `cstarMatrixXLogXDividedDifferenceMonotoneTarget`
- `cstarMatrixBendatShermanDividedDifferenceBridgeTarget`
- `cstarMatrixXLogXPositiveOperatorConvexTarget_of_bendatShermanDividedDifferenceBridge`
- `cstarMatrixBendatShermanDerivativeBridgeTarget`
- `cstarMatrixXLogXPositiveOperatorConvexTarget_of_bendatShermanDerivativeBridge`
- `cstarMatrixRelativeEntropy_algebraMap_real`
- `cstarMatrixRelativeEntropy_algebraMap_real_nonneg`
- `cstarMatrixEntropyVariationalObjective`
- `cstarMatrixEntropyVariationalObjective_liebOptimizer`
- `cstarMatrixRelativeEntropyNonnegOnStrictPositive`
- `cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive`
- `cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_entropyTraceFirstOrder`
- `cstarMatrixEntropyVariationalFormula_of_relativeEntropy_nonneg`
- `cstarMatrixEntropyVariationalFormula`
- `liebTraceConcavityTarget_of_relativeEntropy_route`
- `matrix_isHermitian_cfc_const_one`
- `matrix_isHermitian_cfc_const_neg_one`
- `matrix_isHermitian_cfc_neg_id`
- `matrix_isHermitian_cfc_entropy`
- `matrix_isHermitian_cfc_log_mul_id`
- `matrixTrace_hermitianCfc_entropy_firstOrder_compact_nonneg`
- `cstarMatrix_nonneg_to_matrix_posSemidef`
- `cstarMatrix_isStrictlyPositive_to_matrix_posDef`
- `cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_of_hermitianCfc`
- `cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_hermitianCfc`
- `cstarMatrixEntropyVariationalFormula_of_hermitianCfc`
- `liebTraceConcavityTarget_of_relativeEntropy_jointConvex`
- `cstarMatrix_normedSpaceExp_isTopologicalRing`
- `cstarMatrix_normedRingExp_isTopologicalRing`
- `cstarMatrix_realContinuousFunctionalCalculus`
- `cstarMatrix_log_normedSpace_exp_of_isSelfAdjoint`
- `cstarMatrix_log_cfc_complex_exp_of_isSelfAdjoint`
- `cstarMatrix_log_cfc_real_exp_of_isSelfAdjoint`
- `cstarMatrix_normedRingExp_nonnegSpectrumClass`
- `cstarMatrix_normedSpace_exp_log_of_isStrictlyPositive`
- `cstarMatrix_cfc_complex_exp_log_of_isStrictlyPositive`
- `cstarMatrix_cfc_real_exp_log_of_isStrictlyPositive`
- `cstarMatrix_cfc_realNormalizedLogKernel_eq_unit_interval_integral`
- `cstarMatrix_setIntegral_mono_on`
- `cstarMatrix_cfc_realNormalizedLogKernel_monotone_of_spectrum_bound`
- `cstarMatrix_cfc_realNormalizedLogKernel_monotone`
- `cstarMatrix_cfc_realXLogXDividedDifference_eq_log_add_scaled_normalizedKernel`
- `cstarMatrixXLogXDividedDifferenceMonotoneTarget_of_normalizedLogKernel`
- `matrix_posDef_inverse_schur_block`
- `matrix_weighted_inverse_schur_block`
- `matrix_posDef_weighted_sum`
- `matrix_inv_convex_posDef`
- `cstarMatrix_nonneg_of_matrix_posSemidef`
- `cstarMatrix_le_of_matrix_le`
- `cstarMatrix_cfc_inv_convex_isStrictlyPositive`
- `cstarMatrix_cfc_shifted_inv_eq_cfc_inv_add_smul_one`
- `cstarMatrix_cfc_shifted_inv_convex_nonneg`
- finite-probability Jensen adapters in `CStarMatrixExpectation.lean`
- C-star trace, expectation, order, finite-real embedding, and operator-log
  monotonicity bridges listed in `docs/LIBRARY_LOOKUP.md`
- `cstarMatrix_complex_finiteDimensional`
- `cstarMatrix_compression_add`
- `cstarMatrix_compression_sub`
- `cstarMatrix_compression_smul`
- `cstarMatrix_compression_real_smul`
- `cstarMatrixCompressionCLM`
- `cstarMatrixCompressionCLM_apply`
- `cstarMatrix_compression_one_of_conjTranspose_mul_self_eq_one`
- `cstarMatrix_compression_setIntegral`
- `cstarMatrix_compression_isStrictlyPositive_of_injective_mulVec`
- `cstarMatrixColumnPair_compression_isStrictlyPositive_of_sum`
- `cstarMatrixColumnPair_reflectionAverage_xlog_kernel_corner_of_sum`
- `cstarMatrixColumnPair_reflectionAverage_xlog_corner_of_sum`
- `cstarMatrixXLogXHansenPedersenJensenTarget_of_reflectionAverage_xlog_corner`
- `cstarMatrixXLogXHansenPedersenJensenTarget_of_unit_interval_kernel`

Open dependencies:

- the finite operator-perspective theorem or the trace representation of
  matrix relative entropy through the Kronecker/perspective setup.  The
  finite Kronecker algebra/positivity and trace-normalization facts are
  closed.  The concrete Hansen-Pedersen two-point Jensen theorem for
  \(x\log x\) is also closed locally: ordinary positive-cone operator convexity
  is proved by `cstarMatrixXLogXPositiveOperatorConvexTarget_of_unit_interval_kernel`,
  its all-finite-size packaging by
  `cstarMatrixXLogXPositiveOperatorConvexAllFiniteTarget_of_unit_interval_kernel`,
  the reflection-average nonlinear corner by
  `cstarMatrixColumnPair_reflectionAverage_xlog_corner_of_sum`, and the final
  Jensen target by
  `cstarMatrixXLogXHansenPedersenJensenTarget_of_unit_interval_kernel`.  The
  generic all-functions Hansen-Pedersen transfer theorem is not proved, but it
  is no longer the active blocker for the concrete `x log x` route.  The next
  open source theorem is the Effros perspective/relative-entropy
  joint-convexity layer that turns this concrete Jensen machinery into
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`.
  A Bendat--Sherman alternate route now
  has the derivative-monotonicity subdependency
  `cstarMatrixXLogXDerivativeMonotoneTarget_of_log_monotone`, but still lacks
  the finite Bendat--Sherman theorem converting that monotonicity into
  `cstarMatrixXLogXPositiveOperatorConvexTarget`.  The derivative-only bridge
  is named as `cstarMatrixBendatShermanDerivativeBridgeTarget`; proving it would,
  through
  `cstarMatrixXLogXPositiveOperatorConvexTarget_of_bendatShermanDerivativeBridge`,
  close the operator-convexity input.  The more source-faithful
  Bendat--Sherman route is now also split into the first-divided-difference
  function `realXLogXDividedDifference`, the monotonicity target
  `cstarMatrixXLogXDividedDifferenceMonotoneTarget`, and the bridge
  `cstarMatrixBendatShermanDividedDifferenceBridgeTarget`, with adapter
  `cstarMatrixXLogXPositiveOperatorConvexTarget_of_bendatShermanDividedDifferenceBridge`.
  The divided-difference monotonicity target itself is now closed by
  `cstarMatrixXLogXDividedDifferenceMonotoneTarget_of_normalizedLogKernel`;
  the remaining source-theorem gap is the finite Bendat--Sherman bridge from
  divided-difference monotonicity to operator convexity.  A direct
  integral-representation route now also has finite matrix inverse convexity
  closed by `matrix_inv_convex_posDef`, a finite C-star CFC inverse-kernel
  bridge closed by `cstarMatrix_cfc_inv_convex_isStrictlyPositive`, the
  shifted-positive kernel family closed by
  `cstarMatrix_cfc_shifted_inv_convex_nonneg`, and the corrected
  \(x\log x\) integral representation closed by
  `cstarMatrix_cfc_xlog_eq_unit_interval_xlog_kernel_integral`.  This route
  closed ordinary `x log x` operator convexity, so it is no longer the
  selected blocker;
- any remaining trace-exponential analytic lemmas needed for the full Lieb
  concavity proof beyond the closed real-valuedness/positivity,
  self-adjoint exponential strict positivity, CFC-to-normed-exponential,
  zero-normalization, `log(exp X)=X`, `exp(log A)=A`, scalar/vector
  relative-entropy, relative-entropy diagonal-normalization, scalar-identity,
  and real diagonal matrix bridges;
- matrix relative-entropy joint convexity on the strictly positive cone,
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`.  The chosen Tropp
  monograph route now has the optimizer-candidate equality, normalized
  variational formula, generalized Klein first-order trace inequality,
  matrix relative-entropy nonnegativity, and the reduction from joint
  convexity alone to `liebTraceConcavityTarget H` closed locally by the
  `_of_hermitianCfc` theorems listed above;
- a finite-dimensional proof of Lieb trace concavity for arbitrary
  self-adjoint `H`; this is now reduced to
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive` by
  `liebTraceConcavityTarget_of_relativeEntropy_jointConvex`;
- the nonconditional one-step Tropp trace-MGF inequality after arbitrary-`H`
  Lieb concavity is proved; the Jensen/log-exp composition is closed
  conditionally by
  `FiniteProbability.expectationReal_trace_normed_exp_add_le_of_liebTraceConcavityTarget`;
- iteration of the one-step inequality over independent matrix summands;
- matrix Bernstein/rectangular Bernstein instantiation for the truncated
  Algorithm 1 self-adjoint dilation;
- transfer from the truncated Drineas--Zouzias theorem back to the original
  squared-magnitude distribution when that exact source claim is targeted.

## Failed, Rejected, Or Deferred Routes

- **Direct local/mathlib theorem reuse.** Ruled out in the 2026-05-27 route
  check.  Local and bundled mathlib search found operator-log monotonicity
  (`CFC.log_le_log`) and scalar/real concavity facts, but no ready Lieb trace
  concavity theorem, no Golden--Thompson theorem, no operator-log concavity
  theorem, and no finite matrix Bernstein/Khintchine theorem.  The relevant
  mathlib files still list operator-log concavity as TODO-level infrastructure,
  so the next step must be an actual proof route rather than a small import or
  wrapper.
- **Assume a concentration theorem.** Rejected.  This recreates the hidden
  hypothesis problem and cannot close a paper-level high-probability claim.
- **Use only expectation or deterministic transfer results.** Rejected.  The
  paper claim is high probability in spectral norm.
- **Use the accumulated bounded-increment `sL` bound.** Deferred as a weak
  theorem only.  It ignores zero mean and variance and cannot recover the
  equation (2) rate.
- **Covering-net route.** Deferred.  It avoids Lieb but requires explicit fine
  interval grids, cardinality/radius constants, and sharp fixed-vector scalar
  tails before it can replace matrix Bernstein.
- **Ahlswede--Winter/Golden--Thompson route.** Deferred.  It may be viable but
  is less aligned with the existing Tropp/Lieb infrastructure and may introduce
  different constants or symmetrization obligations.
- **Bendat--Sherman divided-difference route.** Advisory candidate.  The 1955
  monotone/convex operator-functions theorem may provide a route to
  `cstarMatrixXLogXPositiveOperatorConvexTarget` through monotonicity of
  logarithmic divided differences.  The derivative-monotonicity part is now
  proved locally, but the source-faithful route is now represented by
  `cstarMatrixXLogXDividedDifferenceMonotoneTarget` and
  `cstarMatrixBendatShermanDividedDifferenceBridgeTarget`.  The former is now
  closed by `cstarMatrixXLogXDividedDifferenceMonotoneTarget_of_normalizedLogKernel`;
  the bridge itself remains open.
- **Direct shifted-inverse integral route.** Partly closed and no longer the
  selected blocker.  The
  arithmetic-harmonic mean / inverse-convexity dependency is now proved in
  finite complex matrix form by `matrix_inv_convex_posDef`, using Schur
  complements, lifted to finite C-star CFC inverse-kernel convexity by
  `cstarMatrix_cfc_inv_convex_isStrictlyPositive`, and shifted to the
  \(x\mapsto(s+x)^{-1}\), \(s>0\), family by
  `cstarMatrix_cfc_shifted_inv_convex_nonneg`.  The corrected unit-interval
  kernel representation and its CFC integral assembly close ordinary
  positive-cone operator convexity of `x ↦ x log x` via
  `cstarMatrixXLogXPositiveOperatorConvexTarget_of_unit_interval_kernel`.
  This does not close the Hansen-Pedersen transfer theorem, Effros perspective
  theorem, relative-entropy joint convexity, or the matrix concentration
  theorem.

  Weak-component validation for this dependency has two consecutive clean
  passes: focused LSQRSolve build, executable lookup, `git diff --check`,
  touched Lean marker scan, qualified axiom audit, theorem PDF compile,
  targeted text extraction, and rendered-page inspection of the compact-product
  section all passed twice.  The qualified axiom audit reports only standard
  `propext`, `Classical.choice`, and `Quot.sound`.

## Progress Rule

Do not count progress on A1.5-B1 unless one of the open dependencies above is
closed as a Lean theorem, with `#print axioms` checked and the theorem ledger,
not-proved ledger, proof-source ledger, PDF, README, and lookup files updated.
Because this is a red bottleneck, downstream Algorithm 1 spectral theorems,
floating-point transfer corollaries, PDF polish, and lookup prose are frozen as
primary work until a listed dependency closes, a listed route is ruled out with
evidence, or the theorem statement is corrected to match the source claim.

## Latest Dependency Closure

The 2026-05-27 pass closed the self-adjoint matrix-exponential strict
positivity bridge with
`cstarMatrix_normedSpace_exp_isStrictlyPositive_of_isSelfAdjoint`,
`cstarMatrix_cfc_complex_exp_isStrictlyPositive_of_isSelfAdjoint`,
`cstarMatrix_cfc_real_exp_isStrictlyPositive_of_isSelfAdjoint`, and
`liebTraceCfcExp_isStrictlyPositive`.  This reduces the domain side of the
future `log(E[exp X])` trace-MGF theorem.  It does not prove arbitrary-`H`
Lieb trace concavity, trace-MGF domination, matrix Bernstein/Khintchine, or
CACM equation (2).

The same day also closed the conditional one-step Tropp/Jensen adapter
`FiniteProbability.expectationReal_trace_normed_exp_add_le_of_liebTraceConcavityTarget`.
It proves the trace-MGF inequality
`E Re tr exp(H + X) <= Re tr exp(H + log(E exp X))` from the explicit
hypothesis `liebTraceConcavityTarget H`.  This removes the Jensen/log-exp
composition as a separate downstream obstacle, but it does not prove the
arbitrary-`H` Lieb hypothesis itself.

The same pass then closed the first relative-entropy route dependency with
`cstarMatrixRelativeEntropy` and `cstarMatrixRelativeEntropy_self`, naming
the local C-star matrix relative entropy expression and proving `D(A;A)=0`.
This supports the chosen Tropp monograph route to Lieb concavity.  It does not
prove matrix relative-entropy nonnegativity, joint convexity, the variational
principle, Lieb concavity, trace-MGF domination, matrix Bernstein/Khintchine,
or CACM equation (2).

The next focused pass closed the commutative relative-entropy nonnegativity
model with `realRelativeEntropy_nonneg` and
`finiteRealRelativeEntropy_nonneg`.  The scalar proof uses
`log (b/a) <= b/a - 1`; the finite-vector proof sums the scalar inequality
over positive coordinates.  This is a listed foundation for checking the
chosen proof route, but it still does not prove the noncommutative matrix
relative-entropy nonnegativity/joint-convexity or variational theorem required
for arbitrary-`H` Lieb trace concavity.

The following focused pass closed the real scalar-identity matrix case with
`cstarMatrixRelativeEntropy_algebraMap_real` and
`cstarMatrixRelativeEntropy_algebraMap_real_nonneg`.  It proves
`D(aI;bI) = dim * d(a;b)` in the C-star matrix vocabulary and gets
nonnegativity for \(a,b>0\) from the scalar theorem.  This is a genuine
matrix-vocabulary sanity check, but it still does not prove general matrix
relative-entropy nonnegativity, joint convexity, the variational principle,
Lieb concavity, trace-MGF domination, matrix Bernstein/Khintchine, or CACM
equation (2).

The next focused pass closed the real diagonal matrix case with
`cstarMatrixDiagonalStarAlgHom`, `cstarMatrixDiagonalStarAlgHom_continuous`,
`cstarMatrixRealDiagonal`, `cstarMatrixTrace_realDiagonal`,
`cstarMatrix_log_realDiagonal`,
`cstarMatrixRelativeEntropy_realDiagonal`, and
`cstarMatrixRelativeEntropy_realDiagonal_nonneg`.  It proves that the
finite-dimensional diagonal star-algebra embedding is continuous, that the
operator logarithm of a nonzero real diagonal matrix is coordinatewise, and
that C-star matrix relative entropy on real diagonal matrices reduces to the
finite-vector relative entropy.  Thus positive real diagonal matrices satisfy
the commutative diagonal nonnegativity case.  This still does not prove
general noncommutative matrix relative-entropy nonnegativity, joint convexity,
the variational principle, Lieb concavity, trace-MGF domination, matrix
Bernstein/Khintchine, or CACM equation (2).

The following focused pass closed the conditional Tropp relative-entropy route
reduction with `cstarMatrixEntropyVariationalObjective`,
`cstarMatrixEntropyVariationalObjective_liebOptimizer`,
`cstarMatrixRelativeEntropyJointConvexOnStrictPositive`,
`cstarMatrixEntropyVariationalFormula`, and
`liebTraceConcavityTarget_of_relativeEntropy_route`.  A statement-correction
pass fixed the variational objective to include the `Re tr A` constant required
by the local normalization \(D(X;A)=\operatorname{Re}\operatorname{tr}
(X(\log X-\log A)-(X-A))\).  The theorem proves that joint convexity of
local matrix relative entropy on the strictly positive cone, together with
this normalized entropy variational formula for the fixed self-adjoint matrix
\(H\), implies `liebTraceConcavityTarget H`.  The optimizer-candidate equality
part of the variational formula is also closed, and the global
upper-bound/maximality part is reduced to
`cstarMatrixRelativeEntropyNonnegOnStrictPositive` by
`cstarMatrixEntropyVariationalFormula_of_relativeEntropy_nonneg`.  This reduces
the open Lieb dependency to matrix relative-entropy nonnegativity and joint
convexity; it does not prove those foundations, trace-MGF domination, matrix
Bernstein/Khintchine, or CACM equation (2).

The next focused pass used Tropp's proof-source chain to split the
nonnegativity foundation further.  It introduced
`cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive`, the generalized
Klein first-order trace inequality for
\(\Phi(X)=\operatorname{Re}\operatorname{tr}(X\log X-X)\), and proved
`cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_entropyTraceFirstOrder`.
Thus local matrix relative-entropy nonnegativity is now reduced to that
source-aligned first-order trace inequality.  This still does not prove the
first-order trace inequality itself, matrix relative-entropy joint convexity,
Lieb concavity, trace-MGF domination, matrix Bernstein/Khintchine, or CACM
equation (2).

The following pass corrected the theorem family and closed a genuine spectral
dependency from Tropp Proposition 8.3.5.  First,
`cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_of_relativeEntropy_nonneg`
and
`cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_iff_relativeEntropy_nonneg`
show that the local generalized Klein inequality and local matrix
relative-entropy nonnegativity are algebraically equivalent under the current
normalization.  Second, the Hermitian-matrix overlap expansion is now proved:
`matrixTrace_diagonal_mul_mul_diagonal_mul_star`,
`matrixTrace_sum_diagonal_mul_mul_diagonal_mul_star_re`,
`matrixTrace_sum_hermitianCfc_mul_cfc_re`, and
`matrixTrace_sum_hermitianCfc_mul_cfc_nonneg_of_kernel_nonneg`.
This closes the squared-eigenvector-overlap part of Tropp's generalized Klein
proof route.

The next pass closed the scalar/spectral specialization in separated Hermitian
CFC form.  The eigenvalue-local kernel theorem
`matrixTrace_sum_hermitianCfc_mul_cfc_nonneg_of_eigen_kernel_nonneg`, the
four-term first-order adapters
`matrixTrace_hermitianCfc_firstOrderKernel_sum_nonneg` and
`matrixTrace_hermitianCfc_firstOrderKernel_sum_nonneg_of_eigen`, the scalar
entropy kernel `realEntropy_firstOrderKernel_nonneg`, and
`matrixTrace_hermitianCfc_entropy_firstOrder_sum_nonneg` prove the
\(\phi(t)=t\log t-t\) specialization for Hermitian matrices with positive
spectra.  The remaining dependency is now the bridge from that separated
Hermitian-matrix statement to the compact complex `CStarMatrix` logarithm
vocabulary, plus the still-separate joint-convexity foundation.

A further focused pass closed that bridge.  The CFC simplification lemmas
`matrix_isHermitian_cfc_const_one`, `matrix_isHermitian_cfc_const_neg_one`,
`matrix_isHermitian_cfc_neg_id`, `matrix_isHermitian_cfc_entropy`, and
`matrix_isHermitian_cfc_log_mul_id` identify the separated Hermitian expression
with the compact entropy trace inequality
`matrixTrace_hermitianCfc_entropy_firstOrder_compact_nonneg`.  The
C-star-to-plain-matrix positivity bridge is closed by
`cstarMatrix_nonneg_to_matrix_posSemidef` and
`cstarMatrix_isStrictlyPositive_to_matrix_posDef`.  Consequently
`cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_of_hermitianCfc`
proves the local generalized Klein inequality,
`cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_hermitianCfc` proves
local matrix relative-entropy nonnegativity, and
`cstarMatrixEntropyVariationalFormula_of_hermitianCfc` proves the normalized
entropy variational formula.  Finally,
`liebTraceConcavityTarget_of_relativeEntropy_jointConvex` reduces the arbitrary
self-adjoint-`H` Lieb target to the single remaining relative-entropy
foundation, joint convexity.

A follow-up locality search ruled out a hidden local shortcut for that next
dependency.  `rg` over `LeanFpAnalysis`, `docs/LIBRARY_LOOKUP.md`,
`examples/LibraryLookup.lean`, and mathlib found no existing quantum/matrix
relative-entropy joint-convexity theorem, general Lieb trace-concavity theorem,
or matrix Bernstein theorem.  Mathlib does include scalar `convexOn_mul_log`,
but its CFC order files still list operator-log concavity and operator
convexity of `x * log x` as TODOs.  Therefore the next dependency is still a
genuinely new noncommutative matrix-analysis theorem:
`cstarMatrixRelativeEntropyJointConvexOnStrictPositive`, not an unwrapped local
theorem.

The next focused pass closed the commutative joint-convexity layer on the
same route.  The finite log-sum inequality
`finite_log_sum_inequality` is now proved from mathlib's scalar convexity of
\(x\log x\).  It yields scalar and finite-vector joint convexity through
`realRelativeEntropy_jointConvex_of_pos_weights`,
`realRelativeEntropy_jointConvex`, and
`finiteRealRelativeEntropy_jointConvex`.  The C-star diagonal bridge
`cstarMatrixRealDiagonal_smul_add`, positivity helper
`positive_weighted_sum_pos`, and
`cstarMatrixRelativeEntropy_realDiagonal_jointConvex` then prove the real
diagonal subalgebra case of matrix relative-entropy joint convexity.  This is
a route dependency and sanity subcase; it does not prove the noncommutative
strict-cone theorem `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`,
arbitrary-\(H\) Lieb concavity, trace-MGF domination, matrix Bernstein, or
equation (2).

The next focused pass closed the left/right multiplication substrate for the
Effros/Tropp matrix-perspective route.  The local endomorphisms
`cstarMatrixLeftMul` and `cstarMatrixRightMul` now satisfy real affine
weighted-sum laws, commute by `cstarMatrixLeftRightMul_commute`, and are units
when the underlying C-star matrix is a unit or strictly positive.  This is the
algebraic layer needed before building the finite operator-perspective object
\(L_X R_A^{-1}\).  It does not prove operator convexity, the perspective
theorem, the noncommutative strict-cone theorem
`cstarMatrixRelativeEntropyJointConvexOnStrictPositive`, arbitrary-\(H\) Lieb
concavity, trace-MGF domination, matrix Bernstein, or equation (2).

The following focused pass closed the explicit ratio-endomorphism layer for
that same route.  `cstarMatrixLeftRightRatio` names the finite
\(L_XR_A^{-1}\) operator with `A` supplied as a unit,
`cstarMatrixLeftRightRatio_apply` proves it sends \(Z\) to \(XZA^{-1}\), and
`cstarMatrixLeftRightRatio_apply_unit` plus
`cstarMatrixLeftRightRatio_apply_of_isStrictlyPositive` prove the base-point
normalization \((L_XR_A^{-1})(A)=X\).  The next open dependency is still a
genuine finite operator-perspective theorem or the trace representation of
matrix relative entropy through this ratio operator; the noncommutative
joint-convexity theorem itself remains open.

The next focused pass closed the product/power algebra needed before a
functional-calculus trace-representation proof.  `cstarMatrixLeftMul_mul`
proves \(L_{AB}=L_A L_B\), `cstarMatrixRightMul_mul` proves
\(R_{AB}=R_B R_A\), and `cstarMatrixLeftMul_pow`/
`cstarMatrixRightMul_pow` prove compatibility with natural powers.  This is
still only polynomial algebraic substrate: it does not prove continuous
functional calculus for these endomorphisms, the Effros perspective theorem,
the relative-entropy trace representation, or noncommutative joint convexity.

The next focused pass closed the finite Kronecker substrate used in
Tropp/Effros's operator-perspective setup.  Theorems
`matrix_kronecker_left_identity_real_smul_add` and
`matrix_kronecker_right_identity_real_smul_add` prove the real affine laws for
\(A\otimes I\) and \(I\otimes H\); the two product lemmas and
`matrix_kronecker_left_right_commute` prove that these lifts commute and
multiply to \(A\otimes H\); and
`matrix_kronecker_posDef_left_identity`/
`matrix_kronecker_posDef_right_identity` preserve positive definiteness.  This
is still only deterministic Kronecker algebra/positivity substrate: it does
not prove operator convexity, the Effros perspective theorem, the
relative-entropy trace representation, noncommutative joint convexity, Lieb
concavity, trace-MGF domination, matrix Bernstein, or equation (2).

The following focused pass closed the finite Kronecker trace substrate.
`matrix_trace_kronecker` factors
\(\operatorname{tr}(A\otimes H)\) as
\(\operatorname{tr}(A)\operatorname{tr}(H)\), while
`matrix_trace_kronecker_left_identity` and
`matrix_trace_kronecker_right_identity` normalize the identity lifts to
\(d\,\operatorname{tr}(A)\).  This is trace algebra needed before a future
relative-entropy trace-representation proof; it does not prove operator
convexity, the Effros perspective theorem, the representation itself,
noncommutative joint convexity, Lieb concavity, trace-MGF domination, matrix
Bernstein, or equation (2).

An earlier focused pass locked the next source theorem to the finite
Hansen-Pedersen/Effros route.  `cstarMatrixHansenPedersenJensenTwoPointTarget`
names the local two-point Jensen inequality,
`cstarMatrixHansenPedersenJensenTwoPointTarget_id` proves its identity-function
sanity case, and `cstarMatrixXLogXHansenPedersenJensenTarget` records the
positive-cone \(x\log x\) target needed by Effros's perspective proof.  This is
a theorem-statement correction plus a sanity theorem; it does not prove the
nonlinear Hansen-Pedersen theorem, operator convexity of \(x\log x\), the
Effros perspective theorem, the relative-entropy trace representation,
noncommutative joint convexity, Lieb concavity, trace-MGF domination, matrix
Bernstein, or equation (2).

An earlier source-correction pass split that target into the ingredients used
by the cited sources.  `cstarMatrixPositiveOperatorConvexTarget` names the
ordinary positive-cone matrix-convexity hypothesis, and
`cstarMatrixPositiveOperatorConvexTarget_id` proves only its identity-function
sanity case.  The later all-finite correction adds
`cstarMatrixPositiveOperatorConvexAllFiniteTarget` and
`cstarMatrixPositiveHansenPedersenTransferAllFiniteTarget`, because the
standard Hansen--Pedersen block proof uses a larger finite matrix algebra.
The concrete \(x\log x\) route is now represented by
`cstarMatrixXLogXPositiveOperatorConvexAllFiniteTarget` and
`cstarMatrixXLogXHansenPedersenTransferAllFiniteTarget` before the assembled
`cstarMatrixXLogXHansenPedersenJensenTarget`.  This is a theorem-statement
correction that removes two hidden conflations: ordinary convexity versus
transfer, and fixed-size convexity versus all-finite-size convexity. It does
not prove transfer, perspective, concentration, or equation (2).

The next focused pass closed the source-route assembly adapter
`cstarMatrixXLogXHansenPedersenJensenTarget_of_positiveOperatorConvex_of_transfer`.
Thus once `cstarMatrixXLogXPositiveOperatorConvexTarget` and
`cstarMatrixXLogXHansenPedersenTransferTarget` are proved locally, the
assembled `cstarMatrixXLogXHansenPedersenJensenTarget` follows immediately.
This closes only the adapter dependency; the nonlinear operator-convexity and
transfer targets remain open.

After ordinary \(x\log x\) operator convexity closed, the all-finite adapter
`cstarMatrixXLogXHansenPedersenJensenTarget_of_allFiniteTransfer` became the
source-faithful bridge: it packages
`cstarMatrixXLogXPositiveOperatorConvexAllFiniteTarget_of_unit_interval_kernel`
with an all-finite transfer theorem. The active transfer target is therefore
`cstarMatrixXLogXHansenPedersenTransferAllFiniteTarget`.

The next focused bottleneck pass closed the block-compression algebra needed by
that transfer route.  `cstarMatrixBlockDiagonal` and `cstarMatrixColumnPair`
represent \(\operatorname{diag}(T_1,T_2)\) and the block column \(V=[A;B]\).
Theorems `cstarMatrixColumnPair_conjTranspose_mul_self`,
`cstarMatrixBlockDiagonal_mul_columnPair`,
`cstarMatrixColumnPair_conjTranspose_mul_blockDiagonal_mul_columnPair`, and
`cstarMatrixColumnPair_conjTranspose_mul_self_eq_one_of_sum` prove the
isometry/compression identities \(V^*V=A^*A+B^*B\) and
\(V^*\operatorname{diag}(T_1,T_2)V=A^*T_1A+B^*T_2B\).  This removes the
entrywise block-algebra dependency; the remaining red bottleneck is the
nonlinear CFC/Jensen transfer from all-finite ordinary operator convexity.

The following focused pass closed the Bendat--Sherman-route derivative
monotonicity subdependency.  `cstarMatrix_cfc_one_add_log_eq_one_add_log`
normalizes the CFC expression for \(1+\log x\), and
`cstarMatrixXLogXDerivativeMonotoneTarget_of_log_monotone` proves that
\(1+\log x\) is operator-monotone on the strictly positive cone by reusing
`cstarMatrix_log_le_log`.  This is a real closed dependency if the
Bendat--Sherman route is chosen, but it does not prove operator convexity of
\(x\log x\); the missing bridge is the finite Bendat--Sherman theorem.

A later target-lock pass names that missing finite theorem as
`cstarMatrixBendatShermanDerivativeBridgeTarget` and proves the adapter
`cstarMatrixXLogXPositiveOperatorConvexTarget_of_bendatShermanDerivativeBridge`.
This removes the remaining ambiguity in the Bendat--Sherman route: closing the
bridge target would close the concrete \(x\log x\) operator-convexity input,
but the bridge itself remains open and is not used as a hidden hypothesis.

A subsequent source-route correction refines the Bendat--Sherman route to first
divided differences.  `realXLogXDividedDifference` names the scalar divided
difference for \(x\log x\), `cstarMatrixXLogXDividedDifferenceMonotoneTarget`
names the required operator-monotonicity target for all positive base points,
and `cstarMatrixBendatShermanDividedDifferenceBridgeTarget` names the
source-faithful bridge from those divided differences to operator convexity.
The adapter
`cstarMatrixXLogXPositiveOperatorConvexTarget_of_bendatShermanDividedDifferenceBridge`
records exactly what this would close.  The divided-difference monotonicity and
bridge theorems remain open; the derivative monotonicity theorem is only a
closed subdependency/sanity fact.

The latest focused pass closes the scalar normalization dependency for this
route.  `realXLogXDividedDifference_self` records the diagonal value, while
`realXLogXDividedDifference_eq_log_add_ratio` and
`realXLogXDividedDifference_eq_log_add_normalized` rewrite the off-diagonal
first divided difference as the normalized logarithmic kernel
\(\log c + (x/c)\log(x/c)/(x/c-1)\).  This identifies the next actual
operator-theoretic dependency: prove that normalized logarithmic kernel is
operator-monotone, likely by an integral-representation route.  The
operator-monotonicity target and Bendat--Sherman bridge remain open.

The next focused pass closed the first unital inverse-kernel dependency for
that integral-representation route.  `cstarMatrix_spectrum_nonneg_of_nonneg`
exposes real-spectrum nonnegativity for nonnegative finite C-star matrices in
the algebra-module instance shape used by `spectrum ℝ A`.
`cstarMatrix_cfc_one_sub_one_add_inv_monotone` proves operator monotonicity of
\(x \mapsto 1-(1+x)^{-1}\) on the nonnegative cone using unital CFC identities
and C-star inverse antitonicity, and
`cstarMatrix_cfc_pos_over_one_add_monotone` rewrites this as monotonicity of
\(x \mapsto x/(1+x)\).  This is a genuine fractional-kernel subdependency for
the normalized logarithmic-kernel route.  The next dependency closure,
`cstarMatrix_cfc_pos_over_pos_add_monotone`, scales this theorem and proves
operator monotonicity of \(x \mapsto x/(s+x)\) on the nonnegative cone for
every \(s>0\).  The following finite-combination dependency,
`cstarMatrix_cfc_finset_sum_nonneg_mul_pos_over_pos_add_monotone`, proves that
finite nonnegative linear combinations of these scaled kernels remain
operator-monotone.  The generic integral-order dependency
`cfc_integral_mono_of_forall_of_bound` also proves that pointwise CFC Loewner
inequalities pass through a Bochner integral under the joint-continuity and
finite-integral-bound hypotheses of `cfc_integral`.  These closures still did
not, by themselves, prove the scalar/logarithmic integral identity for the
normalized logarithmic kernel, full divided-difference operator monotonicity,
the Bendat--Sherman bridge, Lieb concavity, trace-MGF domination, matrix
Bernstein/Khintchine, or CACM equation (2).

The latest scalar pass closes the off-diagonal identity side of that statement.
`realNormalizedLogKernel` names the diagonal-normalized scalar kernel,
`realXLogXDividedDifference_eq_log_add_normalizedKernel` rewrites the scalar
first divided difference as \(\log c + g(x/c)\), and
`real_normalizedLogKernel_offdiag_intervalIntegral` proves
\[
  \int_0^1 \frac{t}{u+(1-u)t}\,du
  =
  \frac{t\log t}{t-1}
\]
for \(t>0\) and \(t\ne1\).  The remaining dependency is to convert this scalar
representation and the pointwise fractional-kernel monotonicity into CFC
monotonicity of the normalized logarithmic kernel, including the
diagonal/equivalent-a.e. endpoint handling needed by `cfc_integral`.

The newest focused pass closes the interior pointwise integrand theorem:
`cstarMatrix_cfc_unit_interval_fractional_kernel_monotone` proves operator
monotonicity of
\[
  x\mapsto \frac{x}{u+(1-u)x}
\]
for \(0<u<1\) by rewriting it as a positive multiple of
\(x\mapsto x/(s+x)\) with \(s=u/(1-u)\).  The endpoint-inclusive companion
`cstarMatrix_cfc_unit_interval_fractional_kernel_monotone_of_mem_Icc` handles
all \(u\in[0,1]\) on the strictly positive cone: \(u=0\) is the constant-one
CFC kernel and \(u=1\) is the identity kernel.  The next side-condition pass
narrows the route to scalar-integral-to-CFC equality for the normalized kernel;
that equality is closed in the subsequent normalized-kernel pass below.

The next focused pass closes the continuity and boundedness part of those
`cfc_integral` side conditions.  The real-domain theorem
`continuousOn_uncurry_unit_interval_fractional_kernel_spectrum` proves joint
continuity on \([0,1]\times\sigma(A)\) for strictly positive \(A\).  The scalar
bound `real_unit_interval_fractional_kernel_abs_le_max_of_le` proves
\[
  \left|\frac{z}{u+(1-u)z}\right|\le \max(1,M)
\]
for \(u\in[0,1]\) and \(0<z\le M\), while
`real_unit_interval_fractional_kernel_spectrum_norm_le_max` specializes it to
strictly positive spectra.  The a.e. and finite-integral adapters
`ae_unit_interval_fractional_kernel_spectrum_norm_le_max`,
`hasFiniteIntegral_const_max_one_spectrum_bound`,
`continuousOn_uncurry_unit_interval_subtype_fractional_kernel_spectrum`,
`ae_unit_interval_subtype_fractional_kernel_spectrum_norm_le_max`, and
`hasFiniteIntegral_unit_interval_subtype_const_max_one_spectrum_bound` give the
interval-subtype shape expected by the future `cfc_integral` assembly.

The following normalized-kernel pass closes the scalar-integral-to-CFC equality
and the CFC monotonicity theorem for the normalized logarithmic kernel.
`realNormalizedLogKernel_setIntegral` packages the diagonal and off-diagonal
scalar identities.  `cstarMatrix_cfc_realNormalizedLogKernel_eq_unit_interval_integral`
commutes the scalar integral with CFC on strictly positive spectra.
`cstarMatrix_setIntegral_mono_on` isolates the finite C-star-matrix
set-integral order lift and fixes the matrix-order instance diamond explicitly.
Finally, `cstarMatrix_cfc_realNormalizedLogKernel_monotone` proves operator
monotonicity of `realNormalizedLogKernel` on the strictly positive cone.  The
subsequent divided-difference pass closes the base-point scaling/constant-shift
CFC normalization and turns this normalized-kernel theorem into
`cstarMatrixXLogXDividedDifferenceMonotoneTarget`.
`realNormalizedLogKernel_eq_mul_dslope_log` and
`continuousOn_realNormalizedLogKernel_Ioi` supply the continuity needed for
scaling, `cstarMatrix_cfc_realXLogXDividedDifference_eq_log_add_scaled_normalizedKernel`
identifies
\[
  f_c(A)=(\log c)I+g(c^{-1}A),
\]
and `cstarMatrixXLogXDividedDifferenceMonotoneTarget_of_normalizedLogKernel`
closes divided-difference monotonicity.  The remaining Bendat--Sherman-route
dependency is now only the finite divided-difference bridge.

The local-reuse pass also ruled out the easy mathlib route for the next
dependency.  A repository/mathlib search found scalar `convexOn_mul_log` and
operator-log monotonicity, but
`.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Order.lean`
explicitly lists operator-log concavity and operator convexity of
`x => x * log x` as TODOs.  This records a route elimination with evidence:
`cstarMatrixXLogXHansenPedersenTransferAllFiniteTarget` and the assembled
`cstarMatrixXLogXHansenPedersenJensenTarget` must be proved locally from a
source route such as Hansen--Pedersen/Effros, or the proof route must change
deliberately.

The newest focused pass closes a listed dependency for the deliberate direct
integral route.  The finite Schur-complement block theorem
`matrix_posDef_inverse_schur_block`, its positive-combination form
`matrix_weighted_inverse_schur_block`, the endpoint-aware convex-combination
positivity theorem `matrix_posDef_weighted_sum`, and
`matrix_inv_convex_posDef` prove inverse convexity on the finite complex
positive-definite matrix cone.  A follow-up bridge also closes
`cstarMatrix_nonneg_of_matrix_posSemidef`, `cstarMatrix_le_of_matrix_le`, and
`cstarMatrix_cfc_inv_convex_isStrictlyPositive`, giving inverse-kernel
convexity in the finite C-star CFC vocabulary.  A further follow-up closes
`cstarMatrix_cfc_shifted_inv_eq_cfc_inv_add_smul_one` and
`cstarMatrix_cfc_shifted_inv_convex_nonneg`, the shifted inverse-kernel family
needed by the direct integral route.  The scalar normalization bridge
`real_xlog_eq_sub_one_mul_realNormalizedLogKernel` and
`real_xlog_eq_sub_one_mul_normalizedKernel_setIntegral` also now recovers
\(x\log x\) from the normalized logarithmic-kernel integral, and
`real_unit_interval_xlog_integrand_eq_affine_add_shifted_inv` decomposes the
scalar unit-interval integrand into affine plus shifted-inverse form.  This
did not prove the CFC/operator integrand decomposition or operator integral
assembly until the next focused pass.

The next focused pass corrected the direct-route kernel and closed the ordinary
positive-cone operator-convexity dependency.  The source-aligned kernel for
\(x\log x\) is
\[
  \frac{x(x-1)}{u+(1-u)x},
\]
not the auxiliary square kernel.  Theorems
`real_xlog_eq_unit_interval_xlog_kernel_integral`,
`real_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv`,
`cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv`,
`continuousOn_uncurry_unit_interval_xlog_kernel_spectrum`,
`real_unit_interval_xlog_kernel_spectrum_norm_le_max_sq`,
`ae_unit_interval_xlog_kernel_spectrum_norm_le_max_sq`,
`hasFiniteIntegral_const_max_one_spectrum_bound_sq`,
`cstarMatrix_cfc_xlog_eq_unit_interval_xlog_kernel_integral`,
`cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_convex_of_pos_lt_one`,
and `cstarMatrixXLogXPositiveOperatorConvexTarget_of_unit_interval_kernel`
now close `cstarMatrixXLogXPositiveOperatorConvexTarget`, and
`cstarMatrixXLogXPositiveOperatorConvexAllFiniteTarget_of_unit_interval_kernel`
packages that theorem across all finite index types.

The red bottleneck remains open, but the blocker has moved.  Progress now must
close one of the following listed dependencies: the full \(x\log x\)
corner functional-calculus identity \(V^*f((D+RDR)/2)V=f(V^*DV)\) for the range
reflection \(R=2VV^*-I\), assembled from the shifted-inverse kernel corner
identity and the already formalized affine/integral representation; the
source-faithful Hansen--Pedersen transfer target
`cstarMatrixXLogXHansenPedersenTransferAllFiniteTarget`, the assembled
nonlinear operator Jensen theorem, the Effros perspective or matrix relative-entropy
joint-convexity theorem, Lieb trace concavity, trace-MGF domination, matrix
Bernstein/Khintchine, or CACM equation (2).  The
`cstarMatrixBendatShermanDividedDifferenceBridgeTarget` route is now advisory
only for this dependency because ordinary \(x\log x\) operator convexity has
already been proved by the direct integral route.

The latest focused pass closes the shifted-inverse kernel corner dependency
inside that route.  The rectangular unit-inverse adapter
`cstarMatrix_units_inv_mul_rect_eq_mul_units_inv_of_mul_eq` proves that
\(UV=VW\) implies \(U^{-1}V=VW^{-1}\) for rectangular C-star products.  Using
that adapter, `cstarMatrix_cfc_shifted_inv_mul_rect_eq_mul_cfc_shifted_inv_of_mul_eq`
proves that \(EV=VX\) implies
\[
  (sI+E)^{-1}V = V(sI+X)^{-1}
\]
for \(E,X\ge 0\) and \(s>0\), stated through real CFC shifted-inverse kernels.
Finally, `cstarMatrixColumnPair_reflectionAverage_shifted_inv_corner_of_sum`
applies this to \(E=(D+RDR)/2\), \(X=V^*DV\), and the block isometry
\(V=[A;B]\), yielding
\[
  V^*(sI+E)^{-1}V = (sI+V^*DV)^{-1}.
\]
This is a strict dependency closure, not a final transfer theorem.  It was
superseded by the subsequent concrete \(x\log x\) compression/integral
assembly and Hansen--Pedersen Jensen closure.  The current allowed progress
item is the finite Effros perspective / matrix relative-entropy
joint-convexity layer, or a source-backed route elimination for that layer.

Follow-up dependency closure: the affine-corrected normalized entropy kernel
\(x\log x-(x-1)\) has also been formalized.  The new Lean names are
`realEntropyKernel`,
`cstarMatrixEntropyKernelPositiveOperatorConvexTarget`,
`cstarMatrixEntropyKernelPositiveOperatorConvexAllFiniteTarget`,
`cstarMatrixEntropyKernelPositiveOperatorConvexTarget_of_xlog`,
`cstarMatrixEntropyKernelPositiveOperatorConvexTarget_of_unit_interval_kernel`,
`cstarMatrixEntropyKernelPositiveOperatorConvexAllFiniteTarget_of_unit_interval_kernel`,
`cstarMatrixEntropyKernelHansenPedersenJensenTarget`,
`cstarMatrix_cfc_realEntropyKernel_eq_xlog_sub_id_add_one`,
`cstarMatrixEntropyKernelHansenPedersenJensenTarget_of_xlog`, and
`cstarMatrixEntropyKernelHansenPedersenJensenTarget_of_unit_interval_kernel`.
This is a real Effros-route dependency because the normalized relative entropy
is the perspective of that affine-corrected scalar kernel, and Effros consumes
ordinary operator convexity before forming the perspective.  It still does not
prove the finite perspective theorem, the trace representation, or
`cstarMatrixRelativeEntropyJointConvexOnStrictPositive`.

Follow-up dependency closure: the CFC square-root layer for finite perspective
objects is now formalized as well.  The new Lean names are
`cstarMatrixPositiveSqrt`, `cstarMatrixPositiveInvSqrt`,
`cstarMatrixPositiveSqrt_isSelfAdjoint`,
`cstarMatrixPositiveInvSqrt_isSelfAdjoint`,
`continuousOn_real_inv_sqrt_spectrum_of_isStrictlyPositive`,
`cstarMatrixPositiveSqrt_mul_self`,
`cstarMatrixPositiveInvSqrt_mul_sqrt`,
`cstarMatrixPositiveSqrt_mul_invSqrt`,
`cstarMatrixPositiveInvSqrt_isUnit`,
`complex_ofReal_sqrt_mul_self_of_nonneg`,
`cstarMatrixPositiveSqrt_isStrictlyPositive`,
`cstarMatrixPositiveInvSqrt_mul_self_mul`, and
`cstarMatrixPositiveInvSqrt_conj_isStrictlyPositive`.
This closes the local \(A^{1/2}\)/\(A^{-1/2}\) algebraic side conditions for
the next perspective statement.  It also exposes the current route choice more
sharply: the source-faithful route should build the superoperator perspective
on the finite matrix vector space and then prove the trace representation of
Umegaki relative entropy; an ordinary matrix perspective theorem would be true
and now closer, but it would not by itself close
`cstarMatrixRelativeEntropyJointConvexOnStrictPositive`.

Follow-up dependency closure: the ordinary finite perspective theorem for the
normalized entropy kernel is now formalized.  The new Lean names are
`cstarMatrixPerspective`, `cstarMatrixPerspectiveWeight`,
`cstarMatrixPerspectiveWeight_star_mul_self`,
`cstarMatrixPerspectiveWeights_star_mul_self_add`,
`cstarMatrixPerspectiveWeight_compress_normalized`,
`cstarMatrixPerspectiveWeight_mul_positiveSqrt`,
`cstarMatrixPositiveSqrt_mul_perspectiveWeight_star`,
`cstarMatrixPerspectiveWeight_value_uncompress`, and
`cstarMatrixEntropyKernelPerspective_jointConvex`.  This proves joint
convexity of the ordinary finite perspective
\[
  P_f(X,A)=A^{1/2}f(A^{-1/2}XA^{-1/2})A^{1/2}
\]
for \(f(x)=x\log x-(x-1)\).  The red bottleneck is not closed, because the
source route for matrix relative entropy needs the superoperator perspective
on the finite matrix vector space and the trace representation through
\(L_XR_A^{-1}\).  The next allowed progress item is therefore exactly that
superoperator/trace-representation dependency, or a source-backed theorem
statement correction for `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`.

Follow-up dependency closure: the finite vectorization and vectorized-identity
trace pairing are now formalized as listed trace-representation substrate.  The
new Lean names are `matrixVecId`, `matrixVec`,
`matrixComplexQuadraticForm`, `finset_sum_product_diagonal`,
`matrix_kronecker_transpose_mulVec_matrixVec`, and
`matrixComplexQuadraticForm_vecId_kronecker_transpose`, proving that
\(A\otimes B^{\mathsf T}\) represents \(M\mapsto AMB\) and that
\[
  v_I^*(A\otimes B^{\mathsf T})v_I=\operatorname{tr}(AB).
\]
This is exactly the kind of bridge needed to turn Kronecker/superoperator
perspective inequalities back into ordinary trace formulas.  It does not close
the red bottleneck: the missing dependencies are still the CFC/log behavior of
the finite superoperator ratio, the full trace formula for
`cstarMatrixRelativeEntropy`, and then
`cstarMatrixRelativeEntropyJointConvexOnStrictPositive`.

Follow-up dependency closure: the polynomial-power version of the
vectorization/trace-pairing bridge is now formalized.  The new Lean names are
`matrix_kronecker_transpose_pow`,
`matrix_kronecker_transpose_pow_mulVec_matrixVec`, `matrixVec_one`, and
`matrixComplexQuadraticForm_vecId_kronecker_transpose_pow`.  They prove
\[
  (A\otimes B^{\mathsf T})^k=A^k\otimes(B^k)^{\mathsf T},\qquad
  (A\otimes B^{\mathsf T})^k\operatorname{vec}(M)=\operatorname{vec}(A^kMB^k),
\]
and
\[
  v_I^*(A\otimes B^{\mathsf T})^k v_I=\operatorname{tr}(A^kB^k).
\]
This is counted progress on the listed CFC/log superoperator dependency
because it supplies the polynomial trace-representation layer.  It still does
not close the red bottleneck: the missing dependency is now the passage from
polynomials to the required CFC/log expression for the finite left-right ratio,
followed by the full Umegaki relative-entropy trace representation.

Follow-up dependency closure: the finite-polynomial packaging of the preceding
power trace identity is now formalized.  The new Lean names are
`matrixComplexQuadraticForm_sum`, `matrixComplexQuadraticForm_smul`, and
`matrixComplexQuadraticForm_vecId_kronecker_transpose_polynomial`, proving
\[
  v_I^*\left(\sum_{k\in S} c_k(A\otimes B^{\mathsf T})^k\right)v_I
  =
  \sum_{k\in S}c_k\,\operatorname{tr}(A^kB^k).
\]
This closes the finite algebraic polynomial trace layer.  The red bottleneck
now sits at the analytic CFC/log transfer from this polynomial layer to the
finite superoperator ratio and then the full relative-entropy trace formula.

Follow-up dependency closure: the same finite-polynomial trace identity is now
available through Lean's standard `Polynomial.aeval` interface as
`matrixComplexQuadraticForm_vecId_kronecker_transpose_aeval`.  This rules out
one likely API bottleneck for the next CFC/log approximation step.  The
remaining red bottleneck is still analytic rather than algebraic: prove the
functional-calculus/log transfer for the finite superoperator ratio and then
derive the full Umegaki relative-entropy trace representation.

Follow-up dependency closure: the first analytic hook for that transfer is now
formalized as `continuous_matrixComplexQuadraticForm`.  For fixed \(v\), the
map \(M\mapsto v^*Mv\) is continuous on finite complex matrices.  This is
needed to pass polynomial trace-pairing identities through limits.  It does not
close the red bottleneck: the missing pieces are still the approximation/CFC
step for `CFC.log` on the finite superoperator ratio and the full
relative-entropy trace representation.

Follow-up dependency closure: finite matrix polynomial evaluation is now also
proved continuous by `continuous_matrix_polynomial_aeval`.  This complements
the quadratic-form continuity hook and removes another finite-dimensional
continuity side condition for the polynomial-to-CFC route.  The red bottleneck
still remains at the actual approximation/CFC/log theorem and the
relative-entropy trace representation.

Follow-up dependency closure: the superoperator-polynomial perspective layer is
now source-faithful for the Effros/Umegaki route.  The new domain and scalar
approximation names are `matrixVecId_inner_matrixVec`,
`matrix_transpose_conjTranspose_eq_self_of_isSelfAdjoint`,
`matrix_kronecker_transpose_isSelfAdjoint_of_isSelfAdjoint`,
`matrix_kronecker_transpose_posSemidef`, `matrix_kronecker_transpose_posDef`,
`matrix_kronecker_inv_transpose_posDef`, `matrixSelfAdjointCfc`,
`matrixSelfAdjointCfc_polynomial`, `exists_realPolynomial_near_log_on_Icc`,
`exists_realPolynomial_near_xlog_on_Icc`, and
`exists_realPolynomial_near_realEntropyKernel_on_Icc`.  The new trace formulas
are `matrixComplexQuadraticForm_vecId_kronecker_transpose_pow_right`,
`matrixComplexQuadraticForm_vecId_kronecker_transpose_polynomial_right`,
`matrixComplexQuadraticForm_vecId_kronecker_transpose_aeval_right`,
`matrixComplexQuadraticForm_vecId_matrixSelfAdjointCfc_kronecker_transpose_realPolynomial`,
and
`matrixComplexQuadraticForm_vecId_matrixSelfAdjointCfc_kronecker_inv_transpose_realPolynomial_right`.
They prove the finite-polynomial identity
\[
  v_I^*p(L_XR_A^{-1})R_Av_I
  =
  \sum_k p_k\,\operatorname{tr}\!\bigl(X^kA(A^{-1})^k\bigr).
\]
This closes a listed algebraic/CFC-polynomial dependency and removes the hidden
Weierstrass approximation assumption.  The red bottleneck is still not closed:
the next allowed progress item is the analytic logarithmic/entropy-kernel CFC
transfer from these polynomial formulas, followed by the full Umegaki
relative-entropy trace representation.

Follow-up dependency closure: the analytic uniform-approximation transfer is
now formalized.  The new Lean names are
`tendsto_matrixComplexQuadraticForm_matrixSelfAdjointCfc_mul` and
`tendsto_superoperator_entropyKernel_of_realPolynomial_uniform_approx`.  They
prove that uniform convergence on the real spectrum of a finite self-adjoint
matrix passes through matrix CFC, right multiplication, and the vectorized
quadratic-form trace pairing; in the source-faithful ratio case
\(K=X\otimes(A^{-1})^{\mathsf T}\), any explicit real-polynomial uniform
approximation to \(x\log x-(x-1)\) transfers the polynomial formula for
\(v_I^*p(L_XR_A^{-1})R_Av_I\) to the entropy-kernel CFC trace term.  This
closes the listed CFC/log transfer dependency without assuming it as a hidden
hypothesis.  The red bottleneck is reduced but still not closed: the remaining
listed dependency is the full source-faithful Umegaki trace representation and
then `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`.

Follow-up dependency closure: the uniform approximation is now constructed
locally for the positive-definite superoperator spectrum.  The new Lean names
are `matrix_posDef_spectrum_real_pos`,
`matrix_posDef_spectrum_real_subset_Icc`,
`exists_realPolynomial_tendstoUniformlyOn_realEntropyKernel_on_subset_Icc`,
`exists_realPolynomial_tendstoUniformlyOn_realEntropyKernel_spectrum_of_posDef`,
and `exists_realPolynomial_tendsto_superoperator_entropyKernel_trace_of_posDef`.
They prove that positive definite finite matrices have positive real-spectrum
interval bounds, construct real-polynomial entropy-kernel approximants
converging uniformly on that spectrum, and specialize the construction to
\(X\otimes(A^{-1})^{\mathsf T}\).  The red bottleneck is therefore no longer
an approximation-existence question.  It is the source-faithful Umegaki trace
representation from the entropy-kernel CFC trace term, followed by local
matrix relative-entropy joint convexity.

Follow-up dependency correction: the joint-convexity step has been narrowed to
one named source-faithful representation target,
`cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator`.  It states the
Umegaki trace representation through the superoperator ratio \(L_XR_A^{-1}\),
represented by \(X\otimes(A^{-1})^{\mathsf T}\) and right multiplication by
\(A\).  The ordinary source-matrix perspective theorem remains a useful route
dependency, but it is not itself the relative-entropy representation.  The red
bottleneck is therefore this superoperator representation target, followed by
noncommutative relative-entropy joint convexity.

Additional dependency closure: the compact repository relative-entropy trace
has now been expanded into the finite spectral-overlap sum by
`matrixTrace_hermitianCfc_relativeEntropy_re_eq_sum`, with
`matrix_isHermitian_cfc_id` and `matrix_isHermitian_cfc_xlog` supplying the
missing Hermitian CFC simplifications.  This proves the \(D(X;A)\) side of the
Umegaki trace-representation route.  The red bottleneck is now specifically
the superoperator side: prove that
\[
  v_I^* f(L_XR_A^{-1})R_A v_I
\]
for \(f(t)=t\log t-(t-1)\) has the same spectral-overlap expansion, then
transport that equality to the local `CStarMatrix` statement
`cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator`.

Adapter lock: the exact remaining theorem is now named
`matrixSuperoperatorEntropyKernelOverlapExpansion`.  The finite Kronecker
trace term is packaged as `matrixSuperoperatorEntropyKernelTrace`, and
`matrixRelativeEntropyTraceRepresentation_of_superoperator_overlap` proves that
closing the overlap expansion identifies it with the compact relative-entropy
trace already proved by `matrixTrace_hermitianCfc_relativeEntropy_re_eq_sum`.
Future passes should therefore focus on proving the overlap expansion itself,
not on reopening ordinary source-matrix perspective or compact \(D(X;A)\)
algebra.

Dependency closure inside the overlap expansion: the finite-polynomial
approximants now have the required squared-overlap form.  The new Lean names
are `matrix_isHermitian_cfc_congr_eigen`, `matrix_isHermitian_cfc_mul`,
`matrix_isHermitian_cfc_fun_pow_nat`,
`matrix_isHermitian_cfc_inv_of_posDef`,
`matrix_posDef_mul_inv_pow_eq_cfc`,
`matrixTrace_pow_mul_inv_pow_re_eq_sum`, and
`matrixPolynomialTraceRatio_re_eq_sum`.  They prove that
\[
  \operatorname{Re}\operatorname{tr}(X^kA(A^{-1})^k)
  =
  \sum_{i,j}\lambda_i^k\mu_j\mu_j^{-k} |(U_X^*U_A)_{ij}|^2
\]
and that the real-polynomial sum is
\[
  \sum_{i,j}\mu_j p(\lambda_i/\mu_j)|(U_X^*U_A)_{ij}|^2.
\]
This is counted progress because it closes the finite-polynomial overlap
dependency listed under `matrixSuperoperatorEntropyKernelOverlapExpansion`.
The red bottleneck remains open: the next dependency is the limiting passage
from these polynomial overlap formulas to the entropy-kernel CFC trace term.

Dependency closure and red-bottleneck advance: the limiting overlap passage and
source-faithful trace representation are now closed.  The new Lean names are
`realRelativeEntropy_eq_mul_realEntropyKernel_mul_inv`,
`tendsto_matrixPolynomialTraceRatio_overlap_sum_of_uniform_approx`,
`exists_realPolynomial_tendsto_superoperator_entropyKernel_trace_and_overlap_of_posDef`,
`matrixSuperoperatorEntropyKernelOverlapExpansion_of_nonempty`,
`matrixSuperoperatorEntropyKernelOverlapExpansion_of_isEmpty`,
`matrixSuperoperatorEntropyKernelOverlapExpansion_all`, and
`cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator_all`.  These
prove that the entropy-kernel superoperator trace
\[
  v_I^* f(L_XR_A^{-1}) R_A v_I
\]
has the same eigenbasis-overlap expansion as the compact repository
relative-entropy trace, including the empty-index edge case, and transports the
result to the finite `CStarMatrix` statement.

The active red bottleneck is now the noncommutative joint-convexity theorem:

```lean
def cstarMatrixRelativeEntropyJointConvexOnStrictPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ {X Y A B : CStarMatrix ι ι ℂ},
    X ∈ strictPositiveCStarMatrixCone (ι := ι) →
    Y ∈ strictPositiveCStarMatrixCone (ι := ι) →
    A ∈ strictPositiveCStarMatrixCone (ι := ι) →
    B ∈ strictPositiveCStarMatrixCone (ι := ι) →
    ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a + b = 1 →
      cstarMatrixRelativeEntropy (a • X + b • Y) (a • A + b • B) ≤
        a * cstarMatrixRelativeEntropy X A +
          b * cstarMatrixRelativeEntropy Y B
```

Listed dependencies for the next focused pass:

- choose and record the source-faithful proof route from the closed
  superoperator trace representation to relative-entropy joint convexity;
- prove a finite superoperator perspective/joint-convexity theorem, or a
  source-equivalent theorem that directly implies the displayed statement;
- bridge the theorem to `cstarMatrixRelativeEntropy` using
  `cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator_all`;
- preserve all strict-positivity domain assumptions and expose any dimension
  restrictions explicitly;
- do not use the ordinary source-matrix perspective theorem
  `cstarMatrixEntropyKernelPerspective_jointConvex` alone as closure evidence,
  because it is not by itself the Umegaki \(L_XR_A^{-1}\) representation.

Only those dependency closures, route eliminations, or statement corrections
count as progress until `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`
is closed.

Dependency closure inside the joint-convexity bottleneck: the product-index
lift and scalar extraction layers are now formalized.  The new left/right lift
definitions
`cstarMatrixSuperoperatorLeftLift` and `cstarMatrixSuperoperatorRightLift`
represent \(L_X\) by \(X\otimes I\) and \(R_A\) by \(I\otimes A^{\mathsf T}\).
The theorems
`cstarMatrixSuperoperatorLeftLift_real_smul_add`,
`cstarMatrixSuperoperatorRightLift_real_smul_add`,
`cstarMatrixSuperoperatorLeftLift_isStrictlyPositive`, and
`cstarMatrixSuperoperatorRightLift_isStrictlyPositive` close the affine and
strict-positivity domain dependencies for feeding these lifts into the finite
perspective theorem.  The theorems
`matrixComplexQuadraticForm_re_nonneg_of_posSemidef`,
`matrixComplexQuadraticForm_re_mono_of_posSemidef_sub`, and
`matrixComplexQuadraticForm_re_mono_of_cstarMatrix_le` close the real
quadratic-form monotonicity needed to extract a scalar inequality from a
product-index C-star Loewner inequality.

The red bottleneck remains open.  The next listed dependency is the actual
finite superoperator perspective bridge:
\[
  v_I^* P_f(L_X,R_A)v_I
  =
  v_I^* f(L_XR_A^{-1})R_Av_I,
\]
or an equivalent theorem that lets
`cstarMatrixEntropyKernelPerspective_jointConvex` on the product-index lifts
imply joint convexity of `matrixSuperoperatorEntropyKernelTrace`.

Dependency closure inside the joint-convexity bottleneck: the product-index
ordinary perspective inequality itself is now formalized.  The theorem
`cstarMatrixSuperoperatorPerspectiveTrace_jointConvex` proves joint convexity of
the scalar trace pairing
\[
  (X,A)\mapsto v_I^*P_f(L_X,R_A)v_I
\]
by combining `cstarMatrixEntropyKernelPerspective_jointConvex` with the
product-index lift affine/strict-positivity lemmas and real quadratic-form
monotonicity.  The helper `matrixComplexQuadraticForm_add` supplies the scalar
linearity step.

The active red bottleneck has therefore narrowed.  The exact next theorem is:

```lean
def cstarMatrixRelativeEntropyPerspectiveTraceRepresentation
    {ι : Type*} [Fintype ι] [DecidableEq ι] : Prop :=
  ∀ {X A : CStarMatrix ι ι ℂ},
    X ∈ strictPositiveCStarMatrixCone (ι := ι) →
    A ∈ strictPositiveCStarMatrixCone (ι := ι) →
      cstarMatrixRelativeEntropy X A =
        cstarMatrixSuperoperatorPerspectiveTrace X A
```

The conditional theorem
`cstarMatrixRelativeEntropyJointConvexOnStrictPositive_of_perspectiveTraceRepresentation`
proves that this equality bridge implies
`cstarMatrixRelativeEntropyJointConvexOnStrictPositive`.  No downstream theorem
is closed until the equality bridge itself is proved.

Dependency closure inside the equality bridge: the CFC commutation needed to
normalize the ordinary perspective argument is now formalized.  Theorems
`cstarMatrixSuperoperatorLeftLift_rightLift_commute`,
`cstarMatrixSuperoperatorPositiveInvSqrtRightLift_commute_leftLift`, and
`cstarMatrixSuperoperatorPerspective_normalizedArgument_reorder` prove the
chain
\[
  L_XR_A=R_AL_X,\qquad
  R_A^{-1/2}L_X=L_XR_A^{-1/2},\qquad
  R_A^{-1/2}L_XR_A^{-1/2}=L_X(R_A^{-1/2}R_A^{-1/2}).
\]

The next listed dependency is the square-root/inverse bridge
\[
  R_A^{-1/2}R_A^{-1/2}=R_A^{-1}
\]
in the product-index right-lift representation, followed by the CFC equality
between the ordinary product-index perspective trace and
`matrixSuperoperatorEntropyKernelTrace`.

Dependency closure inside the equality bridge: the square-root/inverse bridge
is now formalized.  The theorem
`cstarMatrixPositiveInvSqrt_mul_self_eq_unit_inv` proves the generic strictly
positive C-star identity \(A^{-1/2}A^{-1/2}=A^{-1}\), with inverse expressed as
the inverse unit coming from strict positivity.  The theorem
`cstarMatrixSuperoperatorPerspective_normalizedArgument_eq_leftLift_mul_rightLift_unit_inv`
specializes this to the product-index right lift and combines it with the
normalized-argument reorder, yielding the \(L_XR_A^{-1}\) normalized argument
shape.

The next listed dependency is now the outer perspective/CFC trace bridge:
show that, inside the vectorized-identity quadratic form,
\[
  R_A^{1/2} f(L_XR_A^{-1}) R_A^{1/2}
  =
  f(L_XR_A^{-1}) R_A,
\]
using commutation of \(f(L_XR_A^{-1})\) with \(R_A^{1/2}\), and then identify
the resulting C-star expression with `matrixSuperoperatorEntropyKernelTrace`.

Dependency closure inside the equality bridge: the ratio now commutes with the
outer square root.  Theorems `cstarMatrixPositiveSqrt_commute_unit_inv`,
`cstarMatrixSuperoperatorPositiveSqrtRightLift_commute_leftLift`, and
`cstarMatrixSuperoperatorLeftLift_mul_rightLift_unit_inv_commute_positiveSqrtRightLift`
prove that \(L_XR_A^{-1}\) commutes with \(R_A^{1/2}\).

The next listed dependency is the CFC transport of that commutation:
\[
  f(L_XR_A^{-1})R_A^{1/2}=R_A^{1/2}f(L_XR_A^{-1}),
\]
followed by the quadratic-form equality turning
\(R_A^{1/2}f(L_XR_A^{-1})R_A^{1/2}\) into
\(f(L_XR_A^{-1})R_A\).

Current status update after the relative-entropy/Lieb closure: the equality
bridge, finite-dimensional matrix relative-entropy joint convexity, arbitrary
self-adjoint Lieb trace concavity, and the no-hidden-Lieb one-step Tropp
trace-MGF theorem are now closed.  The active red bottleneck is no longer any
relative-entropy or equality-bridge result; it is Tropp's independent-sum
trace-MGF iteration and matrix Bernstein/Khintchine instantiation for
Algorithm 1 equation (2).

The first product-law dependency for this new bottleneck is also closed in
`LeanFpAnalysis/FP/Algorithms/RandNLA/ElementwiseTraceMGF.lean`.  Theorems
`sqMagSampleProbability`,
`sqMagTraceProbability_expectationComplex_step_eq`,
`sqMagTraceProbability_expectationCStarMatrix_step_eq`,
`sqMagTraceProbability_expectationCStarMatrix_step_eq_sampleExpectation`, and
`sqMagTraceProbability_expectationReal_trace_normed_exp_add_step_le` connect
the one-step theorem to one coordinate of the canonical Algorithm 1
squared-magnitude product trace law.

The exact next theorem family is now an iterated product-law statement:
starting from
`sqMagTraceProbability_expectationReal_trace_normed_exp_add_step_le`, prove a
finite independent-sum trace-MGF domination theorem for
\(\sum_{t<s} X_t\) under `sqMagTraceProbability`, then instantiate it with the
Algorithm 1 self-adjoint dilation residual and the already formalized
zero-mean, variance, and bounded-increment prerequisites.

Dependency status update: the iterated product-law statement is now closed.
`sqMagTraceProbMass_snoc` proves factorization of the appended trace mass,
`sqMagTraceProbability_expectationReal_succ_last_eq` proves last-coordinate
conditioning, and
`sqMagTraceProbability_expectationReal_trace_normed_exp_add_sum_le` proves the
iid trace-MGF domination theorem for arbitrary self-adjoint one-sample
observables under the canonical squared-magnitude trace law.

The red bottleneck has therefore advanced to the matrix Bernstein/Khintchine
tail layer: instantiate the iid trace-MGF theorem with the Algorithm 1
self-adjoint dilation residual increments, use the existing zero-mean,
variance-proxy, and bounded-increment lemmas to bound the logarithmic mean
increment, then combine the resulting trace-exponential bound with the
largest-eigenvalue event bridge.

Dependency status update: the finite-real trace-exponential adapter for that
tail layer is now closed.  The embedding lemmas
`finiteComplexCStarMatrix_zero`, `finiteComplexCStarMatrix_add`, and
`finiteComplexCStarMatrix_finset_sum` prove that finite real sums are
preserved by the C-star embedding.  The bridge theorems
`finiteComplexCStarMatrixRingHom`,
`finiteComplexCStarMatrixRingHom_continuous`,
`finiteComplexCStarMatrix_finiteMatrixExp`,
`cstarMatrixTrace_normed_exp_finiteComplexCStarMatrix`, and
`cstarMatrixTrace_normed_exp_finiteComplexCStarMatrix_re` identify finite real
matrix exponentials and finite real traces with the embedded C-star
trace-exponential.  Finally,
`sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le`
states the Algorithm 1 product-law trace-MGF domination directly in finite real
matrix terms.

The red bottleneck is therefore no longer trace-MGF iteration or real/C-star
transport.  It is the scalar matrix-CGF/log-MGF bound for the Algorithm 1
dilation increments, followed by the final Bernstein/Khintchine
largest-eigenvalue tail conversion and floating-point spectral transfer.

Dependency status update: the trace-MGF theorem is now instantiated with the
actual Algorithm 1 self-adjoint dilation residual increments.  The definition
`sqMagTraceProbabilityFiniteRealTraceMGFLogBound` names the logarithmic
trace-MGF upper-bound expression.  The symmetry lemma
`rectSelfAdjointDilation_elementwiseSampleResidualIncrement_smul_symmetric`
discharges the finite-real trace-MGF side condition for \(\theta D(Z_t)\).
The theorem
`sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_rectSelfAdjointDilation_elementwiseTraceResidual_le`
rewrites the left side as
\(\mathbb E\,\operatorname{tr}\exp(\theta D(A-\widetilde A))\).

Dependency status update: the trace-exponential Markov/eigenvalue interface is
now specialized to the actual scaled Algorithm 1 dilation residual.  The
theorems
`sqMagTraceProbability_eventProb_exists_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_ge_le`
and
`sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_lt_ge`
compose the residual trace-MGF bound with the repository's one-sided and
two-sided eigenvalue Markov interfaces.  The only remaining red dependency is
now the scalar matrix-CGF/log-MGF estimate for the one-sample logarithmic mean
increment, with the explicit Bernstein/Khintchine constants needed for CACM
equation (2).

Dependency status update: the scalar Bernstein parabola and the explicit CFC
Bernstein lift are now closed.  The theorem
`real_exp_mul_le_quadratic_of_nonneg_of_le_one` proves
\(e^{a x}\le 1+a x+(e^a-a-1)x^2\) for \(a\ge0\) and \(x\le1\), while
`real_exp_mul_le_quadratic_scaled_of_nonneg_of_pos_of_le` proves the scaled
\(R>0\) version.  The theorem `cstarMatrix_cfc_quadratic_eq` identifies the
real CFC quadratic \(1+\theta x+\beta x^2\) with
\(I+\theta X+\beta X^2\), and
`cstarMatrix_cfc_real_exp_mul_le_bernstein_quadratic_of_spectrum_le` combines
the scalar inequality with a spectrum upper bound.  The remaining red
dependency is therefore the one-sample matrix-CGF/log-MGF variance-proxy
instantiation and the final Bernstein/Khintchine tail constants.

Dependency status update: the generic one-sample matrix-CGF/log-MGF
variance-proxy theorem is now closed.  The theorem
`FiniteProbability.expectationCStarMatrix_real_smul` supplies real homogeneity
for C-star expectations, `cstarMatrix_cfc_real_exp_mul_eq_normedSpace_exp_real_smul`
identifies the composed CFC exponential with `NormedSpace.exp (theta • X)`,
`cstarMatrix_selfAdjoint_mul_self_nonneg` proves \(X^2\succeq0\), and
`cstarMatrix_log_one_add_le_self_of_nonneg` proves the operator inequality
\(\log(I+B)\preceq B\).  Combining these with the scalar/CFC Bernstein lift
gives
`FiniteProbability.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy`,
which proves
\(\log\mathbb E\exp(\theta X)\preceq g(\theta,R)\mathbb E[X^2]\) for centered
self-adjoint samples with real spectrum bounded above by \(R>0\).  The
remaining red dependency is to instantiate this generic theorem with the
Algorithm 1 self-adjoint dilation residual increments and then complete the
Bernstein/Khintchine tail constants.

Dependency status update: the Algorithm 1 truncated Bernstein skeleton is now
two-sided.  The C-star variance proxy
`sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le`
proves the one-sample dilation second-moment Loewner bound.  The negative
support theorem
`sqMagSampleProbability_neg_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le`
feeds the lower-tail log-CGF route.  The scalar trace-MGF bounds
`sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`
and
`sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`
bound the positive and negative log-CGF trace-MGF expressions by
\((m+n)\exp(s\,g(\theta,L)V)\).  The upper-tail theorem
`sqMagTraceProbability_eventProb_exists_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_ge_le_exp`
and the two-sided theorem
`sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp`
now close the parameterized trace-MGF-to-eigenvalue tail step.  The algebra
lemma `real_exp_neg_log_two_mul_div_mul_self_add` and the explicit corollary
`sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta`
choose \(T=\log(2B/\delta)\), so the two trace-exponential failure terms sum
to \(\delta\).  The remaining red dependency is the optimization of
\(\theta\), conversion from this scaled eigenvalue statement to the exact CACM
equation (2) constants, and downstream floating-point spectral concentration
transfer.

Dependency status update: the deterministic scaled-eigenvalue-to-spectral
conversion is now closed at the unoptimized radius.  The shared spectral
theorem `finiteLoewnerLe_smul_id_of_finiteHermitianEigenvalues_le` proves that
a pointwise Hermitian eigenvalue upper bound implies `M <= L I`, and the
shared algebra theorem `finiteLoewnerLe_of_smul_left_le_smul_id` cancels a
positive scalar from `theta M <= L I`.  The event adapter
`algorithm1ScaledDilationAbsEigenvalueEvent_subset_exactSpectralEvent` converts
`|lambda(theta D(R))| < T` into the rectangular `algorithm1ExactSpectralEvent`
at radius `T/theta`.  Composing this with the explicit `1-\delta` tail gives
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius`,
with radius \(\log(2B/\delta)/\theta\) under \(0<\theta\) and
\(0<\delta\le1\).  The remaining red dependency is therefore narrower:
optimize \(\theta\) and simplify the radius to the source/CACM equation (2)
constants, then compose the exact spectral theorem with the existing
floating-point spectral transfer.

Dependency status update: the scalar theta-optimization dependency is now
closed for the truncated exact route.  The shared scalar theorem
`real_bernstein_exact_radius_le_of_log_le` proves the exact Bennett optimizer
\[
  \theta=\frac{\log(1+Lr/W)}{L}
\]
for a trace-exponential radius of the form
\[
  \frac{q+W(e^{\theta L}-\theta L-1)/L^2}{\theta}.
\]
The monotonicity lemmas `rectOpNorm2Le_mono` and
`algorithm1ExactSpectralEvent_mono` then let
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius`
convert the already proved scaled-radius spectral event into a radius-\(r\)
spectral event under the explicit Bennett budget.  This theorem does not
assume a concentration event; it composes the previously proved trace-MGF
probability theorem with a scalar algebraic optimizer.

The remaining red dependency is now: simplify the Bennett budget to the final
Drineas--Zouzias/CACM equation (2) sample-complexity constants, perform the
truncation transfer at those constants, and then compose the exact spectral
event with the existing floating-point spectral transfer.

Dependency status update: the source-sharp square spectral conversion and
Bennett optimization are now closed.  The new theorems
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius_sharp_square`
and
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius_sharp_square`
repeat the scaled-event and Bennett-radius route with the source-aligned
variance \(V=n\|\widehat A\|_F^2/s^2\) and no-\(\sqrt2\) support radius.  This
does not close the CACM equation (2) paper row yet: the remaining red
dependency is the scalar simplification from the explicit Bennett budget to
the Drineas--Zouzias/CACM sample-complexity constants, followed by truncation
and floating-point transfer at those constants.

Dependency status update: a conservative denominator route is now closed as a
fallback, but it is not the final source-constant route.  The scalar theorem
`real_bennett_transform_lower_bound_two_add` proves
\[
  x^2/(2+x)\le (1+x)\log(1+x)-x \quad (x\ge0),
\]
and `real_bennett_budget_of_quadratic_denominator_two_add` converts
`q <= r^2/(2W+L*r)` into the exact Bennett budget.  Composing this with the
source-sharp square Bennett theorem gives
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bernstein_denominator_sharp_square`.
The red bottleneck is narrowed, not discharged: the source paper uses the
sharper Bernstein denominator \(2W+\frac23 Lr\) and then simplifies that to
the Drineas--Zouzias/CACM sample-complexity constants.

Dependency status update: the sharper source denominator and sample-budget
algebra are now closed for the truncated exact route, and the deterministic
truncation transfer is composed.  The scalar theorems
`real_bennett_transform_lower_bound_two_add_two_thirds` and
`real_bennett_budget_of_quadratic_denominator_two_add_two_thirds` prove the
\(2W+\frac23Lr\) denominator route locally from the logarithm series lower
bound.  The theorem
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_source_sample_budget_sharp_square`
derives the truncated exact event from
\(14n\|A\|_F^2\log(2(2n)/\delta)\le s\varepsilon^2\), and
`sqMagTraceProbability_eventProb_algorithm1ExactTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_square`
adds the deterministic truncation transfer to the original matrix.  The FP
transfer theorem
`sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_square`
is also formalized under an explicit entrywise perturbation budget.

Dependency status update: the support-aware FP perturbation budget is now
closed.  The lemmas `hitCount_le_steps`,
`hitCount_eq_zero_of_forall_not_hit`,
`fl_elementwiseTraceSketch_zero_init_eq_zero_of_forall_not_hit`, and
`sqMagTraceErrorBudget_nonneg` were added to the local elementwise-sampling
library.  The theorem
`fl_elementwiseTraceSketch_zero_init_sqMag_error_bound_of_positiveProb` proves
the entrywise gamma budget on the canonical sampler's positive-probability
support, avoiding any claim about impossible zero-denominator traces.  The
final theorem
`sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_gamma_square`
combines this support event with the exact source-budget event.  This closes
the red A1.5-B1 source-aligned square Algorithm 1 bottleneck; future Algorithm
1 work should only target the distinct untruncated/general-rectangular variant
if it is explicitly kept in scope.

Dependency status update: the distinct literal untruncated route now has a
closed nonconditional theorem surface with an input-dependent reciprocal-entry
radius.  The definitions `elementwiseLiteralContributionRadius` and
`elementwiseLiteralResidualSupportRadius` expose the exact finite support
radius for the literal squared-magnitude law rather than imposing a
no-small-entry floor.  The exact theorem
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_scaled_radius_supportRadius`
uses that radius in the trace-MGF tail.  The FP theorem
`sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_literal_scaled_radius_gamma_supportRadius`
then expands the concrete zero-initialized sketch budget through
`sqMagTraceErrorBudget_zero_init_le_literalContributionRadius` and
`frobNormRect_sqMagTraceErrorBudget_zero_init_le_literalContributionRadius`,
so the final radius contains no hidden budget matrix or generic perturbation
event.  Writing
\[
  G(A)=\sum_{A_{ij}\ne0}\frac{\|A\|_F^2}{|A_{ij}|},
  \qquad H(A)=\|A\|_F+G(A),
\]
the FP additive term is
\(\sqrt{mn}\,\gamma_{s+1}G(A)\).  This closes a corrected literal-law
endpoint.  It does not discharge the source-uniform CACM prose rate for
arbitrarily tiny nonzero entries; that target must either use a different
concentration theorem or be stated with the reciprocal-entry, truncation, or
no-small-entry dependence exposed.

Dependency status update: the same nonconditional literal support-radius
endpoint now has a readable entry-floor specialization.  The deterministic
exact-arithmetic lemmas
`elementwiseLiteralContributionRadius_le_of_entry_abs_ge`,
`elementwiseLiteralResidualSupportRadius_le_of_entry_abs_ge`, and
`smul_elementwiseLiteralContributionRadius_le_of_entry_abs_ge` prove that, if
\(\alpha>0\) and every nonzero entry obeys
\(\alpha\le |A_{ij}|\), then
\[
  G(A)\le mn\,\|A\|_F^2/\alpha,\qquad
  H(A)\le H_\alpha(A)=\|A\|_F+mn\,\|A\|_F^2/\alpha .
\]
The exact wrapper
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_bernstein_denominator_entry_floor`
uses the floor-bound denominator directly, and the FP wrapper
`sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_literal_ge_one_sub_delta_bernstein_denominator_gamma_entry_floor`
charges the rounded sampled-entry rescaling, sketch accumulation, and residual
formation by the explicit radius
\[
  r+\sqrt{mn}\,mn\,\|A\|_F^2\,\gamma_{s+1}/\alpha .
\]
The corresponding sample budget is recorded as
\[
  \Theta\!\left(
    \frac{(\max\{m,n\}\|A\|_F^2+H_\alpha(A)r)\log((m+n)/\delta)}
         {r^2}
  \right).
\]
This is closed, nonconditional, and nonvacuous for fixed positive \(\alpha\),
but it is deliberately not the source-uniform literal CACM rate; the floor is
an explicit theorem hypothesis.

Dependency status update: the finite-test Rademacher signed-matrix primitive
for a Khintchine-style route is now closed.  Theorems
`finiteQuadraticForm_rademacher_signed_matrix_sum_eq_sum` and
`rademacherTraceProbability_eventProb_forall_abs_finiteQuadraticForm_signed_matrix_sum_le_ge_one_sub_sum_two_mul_exp_neg_sq_div`
show that every fixed quadratic form of an exact signed matrix series reduces
to a scalar signed linear form and satisfies the simultaneous finite-family
Hoeffding bound.  This changes the dependency checklist by closing the finite
test-family exact-probability layer, but it does not close the remaining
spectral-tail step for Algorithm 1 copy differences.

Dependency status update: the finite-test theorem is now instantiated on the
actual Algorithm 1 stepwise independent-copy residual-increment differences.
The generalized finite-index theorems
`finiteQuadraticForm_rademacher_signed_matrix_sum_eq_sum_fintype` and
`rademacherTraceProbability_eventProb_forall_abs_finiteQuadraticForm_signed_matrix_sum_fintype_le_ge_one_sub_sum_two_mul_exp_neg_sq_div`
handle the self-adjoint dilation index `Fin m ⊕ Fin n`, and
`sqMagTraceProbability_eventProb_forall_abs_finiteQuadraticForm_rademacher_signed_rectSelfAdjointDilation_sampleResidualIncrement_diff_le_ge_one_sub_sum_two_mul_exp_neg_sq_div`
specializes the exact Rademacher finite-test tail to fixed Algorithm 1 trace
pairs.  This closes the Algorithm-1-specific Rademacherization adapter; the
open dependency is now the noncommutative/spectral upgrade from finite
quadratic-form tests to the all-copy-differences operator event.

Dependency status update: the finite-test-to-operator cover upgrade is now
closed as an exact intermediate theorem.  `MatrixAlgebra.lean` proves
`finiteUnitBallCover` and
`finiteLoewnerLe_of_finite_unit_ball_cover_quadraticForm`, converting finite
quadratic-form tests on a cover into a Loewner upper bound with radius
\(\eta+L(2\rho+\rho^2)\).  `ElementwiseSpectral.lean` proves
`rademacherTraceProbability_eventProb_rectOpNorm2Le_signed_sampleResidualIncrement_diff_ge_one_sub_sum_two_mul_exp_neg_sq_div_of_finiteUnitBallCover`,
which applies that deterministic bridge to fixed Algorithm 1 signed
copy-difference sums under the exact Rademacher law.  This changes the open
dependency: the cover geometry/finite-test handoff is closed, but the coarse
signed-dilation radius \(L\) is still a visible deterministic input.  The
remaining red dependency is a source-uniform matrix Khintchine/Bernstein tail
or another proved route that supplies the needed signed-dilation radius and
then connects it to the all-copy-differences event without reciprocal-entry,
truncation, or no-small-entry assumptions.

Dependency status update: the literal all-copy support event is now formally
known not to hold with probability one.  `ElementwiseSpectral.lean` proves
`algorithm1SmallEntrySupportMatrix_trace_residual_small_unit_diff_not_rectOpNorm2Le`
and the exact-law lower bound
`sqMagTraceProbability_eventProb_not_algorithm1ExactAllCopyDiffSpectralEvent_smallEntry_ge`:
for the one-step input \([1,(|L|+2)^{-1}]\), the all-copy-differences failure
probability is at least the exact tiny-entry sampling probability.  The
quantitative wrapper
`sqMagTraceProbability_algorithm1ExactAllCopyDiffSpectralEvent_smallEntry_delta_ge`
turns this into a necessary condition: any \(1-\delta\) lower bound for the
same literal all-copy event must have \(\delta\) at least the tiny-entry
probability.  Therefore the remaining Algorithm 1 route cannot close CACM
equation (2) by assuming a probability-one literal all-copy support event or a
hidden uniform copy-difference radius.  It must prove an actual
high-probability matrix-tail statement or keep reciprocal-entry, truncation,
or no-small-entry dependence explicit.

Dependency status update: the small-entry obstruction now applies directly to
the literal exact spectral event at arbitrary positive sample count.  The exact
product-law mass theorem
`sqMagTraceProbMass_algorithm1SmallEntrySupportMatrix_all_tiny` and the
deterministic theorem
`algorithm1SmallEntrySupportMatrix_all_tiny_trace_residual_not_rectOpNorm2Le`
show that the all-tiny trace of \([1,(|L|+2)^{-1}]\) has mass
\(p_{\rm tiny}^s\) and violates the radius-\(L\) exact spectral event.  The
probability and delta wrappers
`sqMagTraceProbability_eventProb_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_ge`
and
`sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_delta_ge`
therefore force any \(1-\delta\) claim for that exact spectral event to have
\(p_{\rm tiny}^s\le\delta\).  The logarithmic wrapper
`sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_log_delta_le`
and the divided wrapper
`sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_sample_count_ge`
give \(\log(1/\delta)\le s\log(1/p_{\rm tiny})\) and
\(\log(1/\delta)/\log(1/p_{\rm tiny})\le s\) for \(\delta>0\) and
\(0<p_{\rm tiny}<1\).  The direct incompatibility wrappers
`sqMagTraceProbability_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_of_delta_lt_pow`
and
`sqMagTraceProbability_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_of_sample_count_lt`
then state that the advertised event lower bound is impossible whenever
\(\delta<p_{\rm tiny}^s\), or whenever positive \(\delta\) is paired with a
sample count below the divided logarithmic threshold.  The probability-surface
wrappers
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_all_tiny_smallEntry_le_one_sub_pow`,
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_all_tiny_smallEntry_lt_one`,
and
`exists_delta_not_sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry`
state the same obstruction as
\(\mathbb P(E_{\rm spec})\le1-p_{\rm tiny}^s<1\) and as a fixed-sample
positive-\(\delta\) impossibility.  Thus, for fixed \(L\), the obstruction
imposes the one-sided sample-count order
\(s=\Omega_L(\log(1/\delta))\).  This reduces
the remaining route choice: a
source-uniform literal theorem must use a genuine matrix-tail argument that
absorbs such rare all-tiny traces, or the final theorem must expose
reciprocal-entry, truncation, no-small-entry, or explicit tiny-mass dependence.

Dependency status update: the all-tiny obstruction now has a concrete
source-budget witness.  `ElementwiseSpectral.lean` proves
`real_log_180000_le_18`,
`algorithm1RectSourceBudget_1_2_100_one_div_30000`,
`algorithm1SmallEntrySupportMatrix_100_small_prob_gt_one_div_30000`,
`algorithm1SmallEntrySupportMatrix_100_rect_source_budget_one_div_30000`, and
`sqMagTraceProbability_not_algorithm1ExactSpectralEvent_rect_source_budget_witness`.
For \(m=1\), \(n=2\), \(s=1\), \(L=\varepsilon=100\),
\(\delta=1/30000\), and \(A=[1,1/102]\), the rectangular source-style budget
is true in exact arithmetic, but the literal exact squared-magnitude spectral
event at radius \(100\) cannot have probability at least \(1-\delta\).  This
is exact-law obstruction evidence only.  The wrapper
`not_forall_algorithm1ExactSpectralEvent_of_rect_source_budget_one_div_30000`
now refutes the universal source-budget-only implication at these fixed
parameters.  It does not rule out a different matrix-tail proof, but it rules
out treating the displayed rectangular
source-budget inequality by itself as sufficient for the untruncated literal
law on tiny-entry inputs.

Dependency status update: the active source-sharp Algorithm 2 equation (7)
route has moved from row-sampling setup to the centered covariance CGF layer.
The one-step leverage facts
`leverage_rowOuterGramSample_finitePSD`,
`leverage_rowOuterGramSample_mean_eq_id`, and
`leverage_rowOuterGramSample_finiteLoewnerLe_nat` prove the rank-one sample is
PSD, has mean identity, and is bounded by \(nI\).  The row-trace product-law
adapter in `RowSamplingTraceMGF.lean` then proves the independent trace-MGF
iteration and scalarization bridge for row traces.

Red bottleneck A2.7-CGF:
- Blocking theorem target: instantiate the repository's generic centered
  C-star matrix-CGF/log-MGF variance-proxy theorem with
  \(X_i = \theta(\mathrm{rowOuterGramSample}(U,i)-I)\) under the leverage law
  \(p_i=\|U_{i,*}\|_2^2/n\).
- Required dependencies already closed: finite row probability law, one-sample
  PSD/mean/\(nI\) Loewner facts, C-star embedding/order bridges, support-aware
  generic Bernstein log-CGF theorem, row-trace MGF product-law iteration.
- Next proof dependency: prove the centered observable has C-star expectation
  zero, is self-adjoint, has real spectrum bounded above by \(n-1\) or a
  conservative \(n\), and has a usable variance proxy such as
  \(\mathbb E[(X_i-I)^2]\preceq nI\).
- Failed/avoided route: do not reuse the existing Frobenius/Markov equation
  (7) theorem as a source-sharp concentration theorem; it proves a weaker
  probability bound and cannot close the Oliveira/Tropp row.

Dependency status update: A2.7-CGF is now closed locally.  The new file
`RowSamplingLeverageMGF.lean` proves symmetry/self-adjointness of
\(Y_i-I\), the one-sample C-star zero-mean identity, the conservative spectral
upper bound \(\lambda_{\max}(Y_i-I)\le n\), and
`leverage_rowOuterGramSample_centered_log_cgf_le` by applying the already
formalized generic centered C-star Bernstein log-CGF theorem.  This avoids any
new hidden concentration hypothesis.

Dependency status update: A2.7-tail is now closed in exact finite-Loewner
form.  `RowSamplingLeverageMGF.lean` proves
`leverage_rowOuterGramSample_centered_square_expectationCStarMatrix_eq`,
the negative-centered log-CGF route with radius \(1\), positive and negative
row-trace scalar MGF bounds, one-sided finite-Loewner high-probability tails,
and `leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_exp`.
The delta-budget corollary
`leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_tail_budget`
is deterministic and does not assume concentration.

Dependency status update: A2.7-sample-size is now closed for the explicit
two-denominator Bennett sample-budget form.  The generic scalar bridge
`real_bernstein_tail_le_half_delta_of_quadratic_budget` reuses the local
Bennett transform lower bound and proves the one-sided \(\delta/2\) tail
budget from the displayed sample-size inequality.  The exact theorem
`leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget`
uses separate upper and lower Bennett optimizers, and
`leverageTraceProbability_eventProb_fl_rowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget`
composes the exact event with the local floating-point Gram perturbation budget.

Resolved bottleneck A2.7-sample-size:
- Closed dependency: scalar real Bennett sample-budget simplification.
- Closed dependency: two-sided exact finite-Loewner sample-budget theorem.
- Closed dependency: sharper FP finite-Loewner transfer with
  `rowSampleGramFullFpPerturbBudget fp s U`.
- Residual optional cleanup: derive a single more conservative displayed
  sample-size denominator from the two explicit upper/lower denominators if a
  later exposition wants one hypothesis instead of two.

Dependency status update: the literal rounded sampled-row equation (8) solver
route now has one concrete implementation-backed closure through normal
equations and Cholesky.  The local definitions
`normalEqCholeskyXHat`, `normalEqCholeskyGramBound`,
`normalEqCholeskyRhsBound`, and `normalEqCholeskySolverDx`, together with
`normal_equations_cholesky_forward_error_certificate`, reuse the repository's
`ls_normal_equations_backward` and `ls_normal_equations_forward_error`
theorems to obtain the componentwise solver certificate required by the
rounded sampled-row RandNLA objective theorem.  The final theorem
`leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_normal_eq_cholesky_solver`
closes this normal-equations route without assuming a solver certificate.

Red bottleneck LS.8-rectangular-QR:
- Blocking theorem target: prove that a concrete rectangular QR,
  preconditioned QR, or iterative least-squares implementation for the rounded
  sampled/scaled matrix satisfies either the local `LSQRSolveBackwardError`
  specification or a direct componentwise forward-error certificate usable by
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_forward_error`.
- Required dependencies already closed: literal rounded sampled/scaled
  residual perturbation, deterministic rounded-objective perturbation,
  high-probability rounded-minimizer transfer, additive solver-gap transfer,
  componentwise forward-error transfer, perturbed-Gram solver transfer,
  local QR backward-error-spec adapter, rectangular induced perturbation
  expansion/budget lemmas, norm-budget handoff into the local QR spec,
  rectangular Frobenius invariance under left orthogonal multiplication, and concrete
  normal-equations/Cholesky solver transfer.
- Missing foundation: a rectangular least-squares QR/preconditioner FP theorem
  in the repository's square-matrix framework.  Current local QR files expose
  square QR/Householder interfaces and a local `LSQRSolveBackwardError`
  specification, but not a theorem that a concrete rectangular QR solver
  produces that specification.
- Candidate route A: extend the linear-algebra substrate with rectangular
  Householder QR objects and prove a rectangular QR least-squares backward
  error theorem.
- Candidate route B: formalize a preconditioned iterative least-squares solver
  with an explicit residual/objective gap and feed that gap into the already
  proved solver-gap theorem.
- Candidate route C: keep QR/preconditioner as a named open paper-level row
  and proceed to the next paper algorithm family only after marking this as an
  explicit route choice, not a hidden completed theorem.
- Failed/avoided route: do not advertise the normal-equations/Cholesky closure
  as the paper's QR/preconditioner theorem; it is a valid concrete solver route
  but has different conditioning behavior.

Dependency closure for LS.8-rectangular-QR:
- Closed dependency: bridge source-style perturbed rectangular normal equations
  into the local Gram-system QR specification.  New names:
  `rectLSGram`, `rectLSRhs`, `RectLSNormalEquations`,
  `rectLSGramPerturbation`, `rectLSRhsPerturbation`,
  `rectLSNormalEquations_perturbed_to_gram_system`, and
  `LSQRSolveBackwardError.of_rectangular_perturbed_normal_equations`.
- Closed dependency: expand and bound the induced Gram/RHS perturbations from
  rectangular data perturbations.  New names:
  `rectLSGramPerturbationEntryBudget`,
  `rectLSRhsPerturbationEntryBudget`,
  `rectLSGramPerturbationNormBudget`,
  `rectLSRhsPerturbationNormBudget`,
  `rectLSGramPerturbation_eq_sum`,
  `rectLSRhsPerturbation_eq_sum`,
  `rectLSGramPerturbation_abs_le_entryBudget`,
  `rectLSRhsPerturbation_abs_le_entryBudget`,
  `rectLSGramPerturbation_frobNorm_le_entryBudget`,
  `rectLSGramPerturbation_abs_le_normBudget`,
  `rectLSRhsPerturbation_abs_le_normBudget`, and
  `rectLSGramPerturbation_frobNorm_le_normBudget`.
- Closed dependency: package the norm-budget handoff from perturbed
  rectangular normal equations and rectangular data perturbation bounds into
  the local QR specification.  New name:
  `LSQRSolveBackwardError.of_rectangular_perturbed_normal_equations_normBudget`.
- Closed route-A algebra dependencies: left multiplication of a rectangular
  matrix by a square orthogonal matrix, and right multiplication by a square
  orthogonal matrix, preserve the rectangular Frobenius norm.  New names:
  `matMulRectLeft`, `matMulRectRight`,
  `frobNormSqRect_orthogonal_left`, `frobNormRect_orthogonal_left`,
  `frobNormSqRect_orthogonal_right`, and
  `frobNormRect_orthogonal_right`.
- Closed route-A norm-growth dependency: compatible square left and right
  factors satisfy rectangular Frobenius submultiplicativity.  New names:
  `frobNormRect_eq_frobNormFn`, `frobNormRect_matMulRectLeft_le`, and
  `frobNormRect_matMulRectRight_le`.
- Closed route-A rectangular left-action algebra dependency: identity,
  associativity, and additivity for square left factors acting on rectangular
  matrices.  New names: `matMulRectLeft_id`, `matMulRectLeft_assoc`,
  `matMulRectLeft_add_left`, and `matMulRectLeft_add_right`.
- Closed route-A rectangular one-step accumulation dependency: a perturbed
  square orthogonal transformation applied to an `m × n` matrix preserves the
  source-style representation with a rectangular Frobenius growth bound.  New
  name: `rect_orthogonal_sequence_one_step`.
- Closed route-A rectangular multi-step accumulation dependency: iterating
  supplied perturbed square orthogonal transformations over `m × n` data gives
  a source-style representation with rigorous geometric radius
  `((1+c)^r - 1) ||A||_F`.  New name:
  `rect_orthogonal_sequence_geometric`.
- Closed route-A normal-equation handoff dependency: orthogonal row
  transformations preserve the rectangular Gram matrix, RHS, and normal
  equations.  New names: `rectLSGram_matMulRectLeft_orthogonal`,
  `rectLSRhs_matMulRectLeft_orthogonal`, and
  `RectLSNormalEquations.of_orthogonal_left`.
- Closed route-A right-hand-side accumulation dependency: the same supplied
  perturbed square orthogonal transformations acting on a vector preserve the
  source-style `Qᵀ(b+Δb)` representation and satisfy the rigorous geometric
  Euclidean radius `((1+c)^r - 1) ||b||₂`.  New names:
  `orthogonal_vector_sequence_one_step` and
  `orthogonal_vector_sequence_geometric`.
- Closed route-A top-block solve-exactness dependency: a rowwise
  normal-equation identity implies rectangular normal equations, and if
  transformed QR data has top block `R`, zero lower matrix block, and the
  computed vector solves the top system `R x = c`, then it satisfies the
  rectangular normal equations for the transformed problem even when the lower
  transformed right-hand side is nonzero.  New names:
  `RectLSNormalEquations.of_rowwise_normal` and
  `RectLSNormalEquations.of_top_solve_zero_bottom`.
- Closed route-A floating-point triangular-solve dependency: the repository's
  `backSub_backward_error` theorem now feeds the rectangular QR handoff.
  `RectLSNormalEquations.exists_topBlock_of_fl_backSub` proves that
  `fl_backSub fp n R c` solves a perturbed top system `(R + ΔR)x = c` with
  `|ΔR_ij| ≤ gamma fp n * |R_ij|`; embedding that perturbed block as
  `[R+ΔR;0]` gives rectangular normal equations for the perturbed transformed
  QR problem.  New supporting names: `rectTopBlock`, `rectTopBlock_top`, and
  `rectTopBlock_bottom`.
- Closed route-A common-orthogonal-factor dependency: the matrix and
  right-hand-side accumulation results are now proved simultaneously for one
  common accumulated orthogonal factor `Q`.  This is the shape required by the
  later pullback from transformed QR data to original least-squares data.  New
  names: `rect_orthogonal_matrix_vector_sequence_one_step` and
  `rect_orthogonal_matrix_vector_sequence_geometric`.
- Closed route-A pulled-back top-block dependency: the local `fl_backSub`
  perturbation of the transformed top block is now expressed as an
  original-data perturbation through the common `Q`.  If
  `A_hat = Q^T(A+Delta A)`, `b_hat = Q^T(b+Delta b)`, and `A_hat` has
  shape `[R;0]`, then `fl_backSub(R,c)` satisfies rectangular normal equations
  for `(A+Delta A_total,b+Delta b)` with
  `Delta A_total = Delta A + Q [Delta R;0]` and
  `||Delta A_total||_F <= ||Delta A||_F + ||[Delta R;0]||_F`.  New names:
  `rectTopBlock_add` and
  `RectLSNormalEquations.exists_original_perturbation_of_commonQ_topBlock_fl_backSub`.
- Closed route-A embedded top-block norm-budget dependency: the abstract
  `||[Delta R;0]||_F` term is now discharged from the local triangular-solve
  componentwise budget.  Theorems
  `rectTopBlock_frobNorm_perturb_bound` and
  `rectTopBlock_frobNorm_perturb_bound_of_gamma` prove
  `||[Delta R;0]||_F <= gamma_n ||[R;0]||_F`, and
  `RectLSNormalEquations.exists_original_perturbation_of_commonQ_topBlock_fl_backSub_gamma_bound`
  strengthens the pullback theorem to
  `||Delta A_total||_F <= ||Delta A||_F + gamma_n ||[R;0]||_F`.
  Supporting shared norm adapters:
  `frobNormSqRect_abs` and `frobNormRect_abs`.
- Closed route-A supplied-transform solver-spec dependency: the gamma-budget
  top-block pullback now feeds the local `LSQRSolveBackwardError`
  specification.  The theorem
  `LSQRSolveBackwardError.of_commonQ_topBlock_fl_backSub_gamma_bound_normBudget`
  handles already-transformed common-`Q` data with final `[R;0]` shape and
  explicit induced Gram/RHS norm budgets.  The theorem
  `LSQRSolveBackwardError.of_rect_orthogonal_sequence_topBlock_fl_backSub_gamma_bound_normBudget`
  composes the simultaneous supplied orthogonal-sequence accumulation theorem
  with that common-`Q` wrapper, exposing matrix and right-hand-side radii
  `((1+c)^r - 1)||A||_F` and `((1+c)^r - 1)||b||_2` plus the triangular-solve
  top-block radius `gamma_n ||[R;0]||_F`.
- Closed route-A exact embedded-reflector dependency: the zero-prefix
  Householder lemmas
  `householder_row_eq_id_of_zero_prefix`,
  `householder_col_eq_id_of_zero_prefix`,
  `matMulVec_householder_eq_self_of_zero_prefix`,
  `matMul_householder_eq_self_row_of_zero_prefix`, and
  `matMulRectLeft_householder_eq_self_row_of_zero_prefix` prove that a
  full-size Householder reflector whose vector vanishes on a prefix acts as
  the identity on that prefix, for vectors and square/rectangular matrices.
  This is the exact trailing-reflector algebra needed before a concrete
  rectangular Householder QR implementation can prove that finished
  rows/columns remain undisturbed.
- Closed route-A exact active-column zeroing dependency: the constructed-vector
  definitions `householderActiveVector` and `householderBeta`, together with
  `householderActiveVector_inner_x`,
  `householderActiveVector_inner_self`,
  `householderActiveVector_inner_self_eq_two_inner_x`,
  `householderBeta_mul_activeVector_inner_x`,
  `matMulVec_householder_activeVector_eq_alpha_basis`, and
  `matMulVec_householder_activeVector_eq_zero_of_ne`, prove that the exact
  Householder reflector built from `v = x - alpha e_p` maps `x` to
  `alpha e_p` when `alpha^2 = ||x||_2^2` and `v^T v != 0`.  Thus every
  off-pivot active-column entry is exactly zero.  The nondegeneracy condition
  is explicit; this dependency does not yet provide a floating-point reflector
  construction or rounded panel/update recurrence.
- Closed route-A common panel/update contract dependency:
  `HouseholderPanelAppError` states the exact stronger contract needed for a
  rectangular rounded Householder step: one shared perturbation matrix
  `Delta P` explains both the matrix-panel update and right-hand-side update.
  The theorem
  `householderPanelAppError_rect_orthogonal_matrix_vector_sequence_geometric`
  proves that a sequence of such contracts feeds the existing common-`Q`
  matrix/vector accumulation theorem with the same geometric radii.  This also
  records a statement correction from the bottleneck audit: the vector-only
  `HouseholderAppError` is not strong enough to imply this shared-`Delta P`
  recurrence, because its existential perturbation can differ from vector to
  vector.
- Route correction and closed source-faithful columnwise dependency:
  the stronger shared-`Delta P` contract is not the active source proof route.
  Higham's columnwise Householder QR analysis allows the perturbation matrix
  for a step to depend on the column.  The local route therefore now uses
  `HouseholderColumnwisePanelAppError`,
  `HouseholderColumnwisePanelAppError.of_vector_applications`,
  `orthogonal_vector_sequence_one_step_fixedQ`,
  `rect_orthogonal_columnwise_vector_sequence_geometric`, and
  `householderColumnwisePanelAppError_rect_orthogonal_columnwise_vector_sequence_geometric`.
  These theorems show that independently perturbed columns and the right-hand
  side still share one final exact orthogonal factor `Q`, with columnwise
  radii `((1+c)^r - 1)||A(:,j)||_2` and RHS radius
  `((1+c)^r - 1)||b||_2`.
- Closed exact forward-error adapter dependency:
  `frobNormSq_rankOne`, `frobNorm_rankOne`, `frobNorm_rankOne_smul`, and
  `frobNorm_rankOne_div_vecNorm2Sq` prove the rank-one Frobenius/vector norm
  bridge needed for the perturbation `Delta P = e b^T / ||b||_2^2`.
  `HouseholderAppError.of_forward_error` converts a normwise vector
  forward-error bound into `HouseholderAppError`, handling `b = 0` without a
  hidden nonzero-input hypothesis.  `HouseholderColumnwisePanelAppError.of_forward_errors`
  applies this adapter columnwise to a panel and once to the right-hand side.
- Closed explicit-matrix rounded application dependency:
  `fl_householderApplyExplicit` applies an already formed reflector matrix
  through `fl_matVec`.  The theorem
  `fl_householderApplyExplicit_forward_error_bound` proves
  `||fl(Pb)-Pb||_2 <= gamma_m || |P| ||_F ||b||_2`, and
  `fl_householderApplyExplicit_HouseholderAppError` plus
  `fl_householderApplyExplicitPanel_HouseholderColumnwisePanelAppError`
  instantiate the vector and columnwise contracts.  This route reuses
  `matVec_error_bound`; it does not prove the compact Householder
  dot/scale/subtract primitive.
- Closed compact rounded dot/scale/subtract application dependency:
  `fl_householderApplyCompact` computes `b - beta v (v^T b)` using the local
  rounded dot product, scale, componentwise multiply, and subtraction
  primitives.  The theorem `matMulVec_householder_eq_compact` proves the exact
  identity with `householder`; `fl_householderApplyCompact_componentwise_error_bound`
  and `fl_householderApplyCompact_forward_error_bound` prove the deterministic
  arithmetic budget `householderCompactComponentBudget`; and
  `fl_householderApplyCompact_HouseholderAppError_of_budget` plus
  `fl_householderApplyCompactPanel_HouseholderColumnwisePanelAppError_of_budget`
  instantiate the vector and columnwise contracts under the visible condition
  that the budget norm is at most `c ||b||_2` for the relevant vector.  This
  closes the previously listed low-level compact vector primitive.
- Closed compact sequence-glue dependency:
  `fl_householderApplyCompactPanel_rect_orthogonal_columnwise_vector_sequence_geometric`
  composes the compact panel/RHS routine and visible budget-domination
  hypotheses with the existing columnwise geometric accumulation theorem.  A
  supplied compact reflector sequence now yields one accumulated orthogonal
  factor plus columnwise data and RHS perturbation radii.
- Closed compact sequence-to-solver-spec handoff dependency:
  `frobNormRect_le_of_col_vecNorm2_le` converts the columnwise perturbation
  radii into a Frobenius data radius, and
  `LSQRSolveBackwardError.of_compact_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget`
  feeds the compact sequence theorem, final `[R;0]`/top-RHS hypotheses, and
  rounded top-block triangular solve into the local `LSQRSolveBackwardError`
  specification.  This closes the previous gap between the columnwise compact
  route and the solver-facing interface; the final QR loop shape hypotheses are
  still explicit.
- Closed exact trailing Householder shape dependency:
  the earlier full-vector active-column theorem was not the final QR shape
  theorem, because rectangular QR reflectors are built from the trailing pivot
  segment and must have a zero prefix.  The new definitions
  `householderPrefixPart`, `householderTrailingPart`,
  `householderTrailingNorm2Sq`, and `householderTrailingActiveVector` express
  that source-faithful construction.  The theorem
  `matMulVec_householder_trailingActiveVector_eq_prefix_alpha_zero` proves that
  the exact reflector preserves entries above the pivot, maps the pivot to
  `alpha`, and zeros entries below the pivot.  The theorem
  `exact_trailing_householder_sequence_lower_zero` proves the exact
  lower-trapezoidal zero invariant for a supplied exact trailing Householder
  recurrence.  Finally, `rectangular_topBlock_shape_facts_of_lower_zero`
  converts that lower-zero invariant into the solver-facing `[R;0]` shape,
  `cTop` definition, and upper-triangular `R`.
- Closed stored rounded shape dependency:
  `fl_householderStoredPanelStep` models the algorithmic storage convention for
  rounded QR: compact-update active/trailing entries, preserve completed
  columns, and explicitly write zeros below the active pivot.  The sequence
  theorem `fl_householderStoredPanel_sequence_lower_zero` proves the final
  lower-trapezoidal zero pattern, and
  `fl_householderStoredPanel_sequence_topBlock_shape_facts` converts it into
  the solver-facing `[R;0]`, `cTop`, and upper-triangular facts.
- Closed stored-step perturbation contract dependency:
  `householderCompactComponentBudget_nonneg`,
  `fl_householderStoredRhsStep_componentwise_error_bound`,
  `fl_householderStoredRhsStep_forward_error_bound`,
  `fl_householderStoredPanelStep_column_componentwise_error_bound`,
  `fl_householderStoredPanelStep_column_forward_error_bound`, and
  `fl_householderStoredPanelStep_HouseholderColumnwisePanelAppError_of_budget`
  show that the stored compact panel/RHS step satisfies
  `HouseholderColumnwisePanelAppError` under explicit preservation,
  pivot-zeroing, RHS-prefix, and budget-domination hypotheses.  This directly
  links the storage convention to the columnwise common-`Q` perturbation
  contract; it intentionally does not hide the remaining loop proof obligations
  as assumptions.
- Closed one-step trailing-reflector discharge dependency:
  `fl_householderStoredTrailingPanelStep_HouseholderColumnwisePanelAppError_of_budget`
  proves that, for the QR trailing Householder vector, the pre-step lower-zero
  invariant implies completed-column preservation, the zero-prefix reflector
  preserves the RHS prefix, and the trailing active-vector theorem zeros the
  stored pivot column below the diagonal.  Thus one stored trailing step
  satisfies `HouseholderColumnwisePanelAppError` under the visible denominator
  and budget-domination hypotheses.
- Closed multi-step stored trailing loop dependency:
  `fl_householderStoredTrailingPanel_rect_orthogonal_columnwise_vector_sequence_geometric`
  invokes the one-step trailing-reflector theorem at every pivot using the
  stored lower-zero invariant.  It supplies one common orthogonal factor,
  columnwise data perturbation radii, and an RHS perturbation radius for the
  final stored outputs under explicit Householder denominator and compact
  budget-domination hypotheses.
- Closed stored-loop solver-spec handoff dependency:
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget`
  composes the multi-step stored perturbation theorem with the stored final
  `[R;0]`/`cTop` shape facts, the Frobenius/column bridge, and the existing
  `fl_backSub` pullback into a solver-facing `LSQRSolveBackwardError`.
- Closed per-pivot FP nonbreakdown bridge:
  `fl_householderStoredTrailingPanelStep_diag_nonzero_of_budget_lt_abs_alpha`
  proves a stored pivot is nonzero when its componentwise compact-update
  budget is smaller than `|alpha|`;
  `fl_householderStoredPanel_sequence_diag_nonzero_of_step_diag_nonzero`
  carries one-step pivot nonzeroness to the final diagonal by completed-column
  preservation; and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_pivot_error_lt_abs_alpha`
  uses this generated diagonal proof in the stored-loop solver certificate.
- Closed pivot-value denominator nonbreakdown bridge:
  `householderTrailingActiveVector_inner_self_ne_zero_of_pivot_ne_alpha`
  proves the Householder denominator `v^T v != 0` from the scalar condition
  `A_hat[k,k] != alpha_k`; `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_pivot_ne_alpha`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_pivot_ne_alpha_and_pivot_error_lt_abs_alpha`
  use this generated denominator proof in the stored-loop solver certificate.
- Closed sign-choice denominator nonbreakdown bridge:
  `householder_pivot_ne_alpha_of_trailingNorm2Sq_pos_mul_nonpos` proves
  `A_hat[k,k] != alpha_k` from the standard local sign-choice facts
  `alpha_k^2 = ||A_hat_k(k:m,k)||_2^2`,
  `0 < ||A_hat_k(k:m,k)||_2^2`, and
  `alpha_k * A_hat[k,k] <= 0`; the QR and LSQRSolve wrappers
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_trailingNorm_pos_mul_nonpos`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_trailingNorm_pos_mul_nonpos_and_pivot_error_lt_abs_alpha`
  use this generated denominator proof in the stored-loop solver certificate.
- Closed scalar lower-bound bridge:
  `householderTrailingNorm2Sq_pos_of_exists_ne` reduces
  `0 < ||A_hat_k(k:m,k)||_2^2` to a concrete nonzero active trailing entry,
  `householderTrailingNorm2Sq_pos_of_pivot_ne_zero` handles the pivot-entry
  special case, and `budget_lt_abs_alpha_of_lt_sqrt_trailingNorm2Sq` reduces
  `budget_k < |alpha_k|` to a square-root lower bound on the active trailing
  norm using `abs_alpha_eq_sqrt_trailingNorm2Sq`.
- Closed prefix-span nonbreakdown bridge:
  `qrColumnNotInPreviousSpan` states that the current pivot column is not in
  the span of previous columns, and
  `qrPrefixSupportSpannedByPreviousColumns` states that the previous columns
  span every vector supported on the already-finished prefix.  The theorems
  `exists_active_trailing_entry_ne_of_column_notInPreviousSpan` and
  `householderTrailingNorm2Sq_pos_of_column_notInPreviousSpan` prove that
  these invariants supply a nonzero active trailing entry and a positive
  trailing norm.  The wrapper
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_sqrt_budget`
  combines that with sign choice and a square-root budget to prove final
  nonzero stored diagonal entries.
- Closed prefix-span coefficient bridge:
  `qrPrefixBasisCoefficientMatrix` states that a concrete coefficient matrix
  reproduces the first `k` coordinate basis vectors using previous columns on
  the prefix rows, and
  `qrPrefixSupportSpannedByPreviousColumns_of_prefixBasisCoefficientMatrix`
  proves that this witness plus the QR lower-zero shape gives
  `qrPrefixSupportSpannedByPreviousColumns`.
- Closed leading-block inverse orientation adapter:
  `qrPreviousLeadingBlockTranspose` packages the transpose of the leading
  `k × k` block, and
  `qrPrefixBasisCoefficientMatrix_of_leftInverse_previousLeadingBlockTranspose`
  reuses `IsLeftInverse` to produce the prefix coefficient witness.
- Closed leading-column left-inverse bridge:
  `qrLeadingColumnLeftInverse` states that a concrete dual coefficient family
  selects the first `k+1` columns, and
  `qrColumnNotInPreviousSpan_of_leadingColumnLeftInverse` proves that this
  witness supplies `qrColumnNotInPreviousSpan`.
- Closed leading-block inverse padding adapter:
  `qrLeadingBlock` names the actual leading `(k+1) x (k+1)` block, and
  `qrLeadingColumnLeftInverse_of_leftInverse_leadingBlock` pads a local
  `IsLeftInverse` witness by zeros outside the first `k+1` rows to produce
  the ambient leading-column dual witness.
- Closed concrete leading-witness composition bridge:
  `exists_active_trailing_entry_ne_of_leading_witnesses`,
  `householderTrailingNorm2Sq_pos_of_leading_witnesses`, and
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_witnesses_sqrt_budget`
  combine the coefficient witness, left-inverse witness, QR lower-zero shape,
  sign choice, and explicit square-root budget to prove stored-loop diagonal
  nonbreakdown without separately assuming the abstract prefix-span and
  column-independence invariants.
- Closed local-inverse composition bridge:
  `exists_active_trailing_entry_ne_of_leading_block_leftInverses`,
  `householderTrailingNorm2Sq_pos_of_leading_block_leftInverses`, and
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_block_leftInverses_sqrt_budget`
  compose local `IsLeftInverse` witnesses for the transposed previous leading
  block and actual leading block directly into active trailing nonbreakdown and
  stored-loop diagonal nonbreakdown.
- Closed determinant/rank local-inverse bridge:
  `nonsingInv`, `isLeftInverse_nonsingInv_of_det_isUnit`, and
  `exists_isLeftInverse_of_det_ne_zero` turn a nonzero determinant into the
  repository's `IsLeftInverse` predicate, and the QR wrappers
  `qrPrefixBasisCoefficientMatrix_of_det_ne_zero_previousLeadingBlockTranspose`,
  `qrLeadingColumnLeftInverse_of_det_ne_zero_leadingBlock`,
  `exists_active_trailing_entry_ne_of_leading_block_det_ne_zero`,
  `householderTrailingNorm2Sq_pos_of_leading_block_det_ne_zero`, and
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_block_det_ne_zero_sqrt_budget`
  consume nonzero determinants of the relevant local leading blocks in the
  stored-loop nonbreakdown theorem.
- Closed triangular principal-minor determinant route:
  `det_ne_zero_of_upper_triangular_diag_ne_zero` and
  `det_ne_zero_of_lower_triangular_diag_ne_zero` prove that triangular finite
  real matrices with nonzero diagonal have nonzero determinant.  The QR
  adapters
  `qrPreviousLeadingBlockTranspose_det_ne_zero_of_upper_triangular_diag_ne_zero`
  and `qrLeadingBlock_det_ne_zero_of_upper_triangular_diag_ne_zero` instantiate
  those shared algebra facts on the previous and current local leading blocks.
  This closes a listed determinant-generation route under visible triangular
  shape and nonzero local diagonal assumptions.  It is not a proof that generic
  full column rank implies every current leading principal block is
  nonsingular.
- Closed solver-facing nonsingular-leading-block route:
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_leading_block_det_ne_zero_sqrt_budget`
  pushes nonzero local leading-block determinants, QR lower-zero shape, sign
  choice, square-root pivot budgets, compact panel/RHS budget domination, and
  final Gram/RHS norm budgets all the way into the local
  `LSQRSolveBackwardError` certificate.  This removes another solver-handoff
  layer from the bottleneck and has two clean weak-component passes, but it
  does not prove the determinant/rank facts or the square-root budget lower
  bound themselves.
- Closed triangular-leading-block solver route with two weak-component passes:
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_triangular_leading_blocks_sqrt_budget`
  composes the triangular determinant adapters with the solver-facing
  nonsingular-leading-block wrapper.  This closes the visible
  triangular-principal-minor route into `LSQRSolveBackwardError` under
  explicit upper-triangular shape, nonzero leading diagonals, sign choice,
  square-root pivot budgets, compact update budgets, and final Gram/RHS
  budget hypotheses.  It is not a proof that generic full column rank implies
  those current leading principal minors are nonsingular, and it keeps the
  square-root budget lower bound visible.
- Remaining active dependency: prove those local leading-block determinants
  are nonzero from a formal rank/nonbreakdown invariant, or use the new
  triangular-principal-minor adapters under visible nonzero local diagonal
  assumptions; and prove a usable square-root trailing-norm lower bound from a
  formal conditioning or nonbreakdown invariant for the computed loop.  Until
  that route is formalized, these are visible triangular-solve domain
  conditions.
- Closed a smaller square-root budget dependency with two weak-component passes:
  `budget_lt_sqrt_householderTrailingNorm2Sq_of_lt_abs_active_entry` proves
  that a concrete active-entry magnitude lower bound `budget < |x_i|` with
  `i >= k` implies the square-root trailing-norm budget.  The remaining
  quantitative bottleneck is now to derive such an active-entry lower bound
  from rank/nonbreakdown/conditioning, or keep it visible as a domain
  assumption.
- Active-entry stored-loop wrapper closed with two weak-component passes:
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_active_entry_budget`
  lifts the scalar active-entry bridge into final stored diagonal nonbreakdown
  under prefix-span nonbreakdown, sign choice, and Householder normalization.
  This is a listed dependency closure path, but it still keeps the active-entry
  magnitude lower bound visible.
- Solver-facing active-entry wrapper closed with two weak-component passes:
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_active_entry_budget`
  pushes the same prefix-span plus active-entry route into the least-squares QR
  certificate.  This is a direct listed dependency closure, not a proof of the
  active-entry lower bound from rank or conditioning.
- Dimensioned norm-square-budget wrapper closed with two weak-component passes:
  `exists_active_entry_budget_lt_abs_of_dim_mul_budget_sq_lt_trailingNorm2Sq`
  proves that `m * budget^2 < trailingNorm2Sq` supplies the active-entry witness
  needed by the previous route.  The stored-loop theorem
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_trailingNorm2Sq_budget`
  and solver theorem
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_trailingNorm2Sq_budget`
  lift that finite margin into QR diagonal nonbreakdown and the local
  `LSQRSolveBackwardError` certificate.  This narrows the quantitative
  bottleneck to a cleaner statement: derive the per-pivot margin
  `m * budget_k^2 < trailingNorm2Sq_k` from conditioning/nonbreakdown, or keep
  that margin as a visible domain assumption.
- Leading-dual norm lower-bound route closed with two weak-component passes:
  `householderTrailingNorm2Sq_ge_inv_leading_dual_norm_budget` proves that a
  pivot-selecting leading dual row with `||L_last||_2^2 <= K` and prefix-span
  gives `1 / K <= trailingNorm2Sq_k`.  The wrappers
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leading_dual_norm_budget`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leading_dual_norm_budget`
  use `m * budget_k^2 < 1 / K_k` to feed the dimensioned norm-square route.
  This is progress only because it closes a listed quantitative dependency:
  the next red-bottleneck dependency is to construct/bound the dual from a
  concrete local inverse, determinant margin, SVD, or condition-number theorem,
  or to keep the dual-norm budget visible as a domain assumption.
- Local leading-block inverse row-norm route closed with two weak-component passes:
  `vecNorm2Sq_qrLeadingRow_padded_eq` and
  `qrLeadingColumnLeftInverse_padded_row_norm_sq_eq` prove that the last row of
  a local left inverse for the concrete leading block pads to the ambient dual
  row with the same squared norm.  The stored-loop theorem
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget`
  and solver theorem
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget`
  close the local-inverse version of the leading-dual dependency under
  `||C_k(k,:)||_2^2 <= K_k` and `m * budget_k^2 < 1 / K_k`.  This reduces the
  next red-bottleneck dependency to deriving or bounding that inverse-row norm
  from an inverse norm, determinant margin, SVD, condition number, or keeping it
  visible as a domain assumption.
- Local leading-block inverse Frobenius-norm route closed with two
  weak-component passes:
  `vecNorm2Sq_row_le_frobNormSq` and `vecNorm2Sq_row_le_frobNorm_sq` show that
  the local inverse row budget follows from a local inverse Frobenius budget.
  The QR and solver wrappers
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget`
  close the stored-loop and solver-facing certificates under
  `||C_k||_F^2 <= K_k` and `m * budget_k^2 < 1 / K_k`.  This closes a listed
  inverse-norm dependency with two clean passes, but it still does not derive
  `||C_k||_F` from determinant margins, SVD, or condition numbers.
- Local leading-block inverse infinity-norm route closed with two
  weak-component passes:
  `abs_coord_le_sum_abs`, `vecNorm2Sq_le_sum_abs_sq`,
  `frobNormSq_le_nat_mul_infNorm_sq`, and
  `frobNorm_sq_le_nat_mul_infNorm_sq` prove
  `||C_k||_F^2 <= (k+1)||C_k||_\infty^2`.  The QR wrappers
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget`
  and the solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget`
  close the same visible-domain route under
  `(k+1)||C_k||_\infty^2 <= K_k` and
  `m * budget_k^2 < 1 / K_k`.  This is now a listed dependency closure with
  two clean passes; it still does not derive the inverse infinity norm from
  triangular inverse estimates, determinant margins, SVD, or condition numbers.
- Diagonal-dominant triangular inverse route closed with two passes:
  `triInv_infNorm_upperBound` and
  `triInv_infNorm_sq_budget_of_diagDominantUpper` reuse the local Higham
  inverse-bound file to derive the inverse infinity-norm budget from
  `IsDiagDominantUpper` plus a full inverse and an explicit diagonal-minimum
  budget.  The solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_diagDominant_leadingBlock_invNorm_budget`
  pushes this into the stored QR least-squares certificate.  This branch now
  has two clean weak-component passes.  It still leaves open whether the
  computed leading blocks are diagonal dominant, or whether a
  determinant/SVD/condition-number route should replace that domain assumption.
- Determinant-facing diagonal-dominant route closed with two validation passes:
  `isInverse_nonsingInv_of_det_ne_zero` and
  `triInv_infNorm_sq_budget_of_diagDominantUpper_det_ne_zero` remove the
  explicit inverse witness from the diagonal-dominant branch under
  `det S_k != 0`.  The solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_diagDominant_leadingBlock_det_ne_zero_invNorm_budget`
  pushes this into the stored QR least-squares certificate.  This is a listed
  dependency closure; it still leaves
  diagonal dominance, determinant nonzero, and the diagonal-minimum budget as
  visible source/domain assumptions.
- Determinant-facing inverse-norm route closed with two validation passes:
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_infNorm_budget`
  uses `det S_k != 0` to set `C_k = nonsingInv S_k` in the inverse-\(\infty\)
  route.  This removes the explicit local inverse witness without assuming
  diagonal dominance, but it still leaves the inverse-\(\infty\) budget,
  determinant hypothesis, prefix-span, and solver budgets visible.  This is a
  listed dependency closure; the remaining red-bottleneck route is to derive
  the visible inverse-\(\infty\) budget from SVD, condition-number,
  determinant-margin, or computed-loop assumptions, or to keep it as an
  explicit domain assumption.
- Condition-number route closed with two weak-component passes:
  `infNorm_eq_sup_row_sum`, `kappaInf_eq_infNorm_mul_infNorm`, and
  `infNorm_sq_budget_of_kappaInf_le_and_norm_lower` bridge Higham's
  `kappaInf` definition to the repository infinity norm and derive the local
  inverse-\(\infty\) budget from a positive lower norm bound and a visible
  condition-number bound.  The solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_kappaInf_budget`
  feeds this budget into the determinant-facing inverse-norm route.  This is a
  listed dependency closure, but it still leaves the local `rho_k`, `kappa_k`,
  determinant, prefix-span, compact-update, sign-choice, and final solver-budget
  assumptions visible.  The remaining red-bottleneck work is to derive these
  local conditioning/nonsingularity assumptions from SVD, determinant-margin, or
  QR-loop invariants, or explicitly keep them as domain assumptions.
- Self-norm condition-number route closed with two weak-component passes:
  `infNorm_pos_of_det_ne_zero` proves that a nonempty nonsingular local leading
  block has positive repository infinity norm.  The determinant-facing
  perturbation lemmas `infNorm_inv_le_of_kappaInf_le_and_det_ne_zero` and
  `infNorm_sq_budget_of_kappaInf_le_and_det_ne_zero` therefore specialize the
  previous route with `rho_k = ||S_k||_infty`, and the solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_kappaInf_selfNorm_budget`
  removes the separate lower-norm parameter.  This will count as a listed
  dependency closure; it still leaves
  `det S_k != 0`, the local `kappaInf` bound, prefix-span, compact-update,
  sign-choice, and final solver budgets visible.
- Closed prefix-span bridge for the self-norm condition-number route:
  `qrPrefixSupportSpannedByPreviousColumns_of_det_ne_zero_previousLeadingBlockTranspose`
  derives the abstract prefix-span invariant from `det T_k != 0` for the
  previous transposed leading block and the completed-column lower-zero shape.
  The solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_leading_blocks_det_ne_zero_kappaInf_selfNorm_budget`
  removes the abstract prefix-span hypothesis from the self-norm `κ∞` route.
  Two weak-component passes passed, so this counts as a listed dependency
  closure; it still leaves previous/current determinant assumptions, local
  condition-number bounds, sign choice, compact-update budgets, and final
  solver budgets visible.
- Closed triangular self-norm condition-number route:
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_triangular_leading_blocks_kappaInf_selfNorm_budget`
  derives the previous/current determinant hypotheses and the completed-column
  lower-zero shape from visible upper-triangular local shape plus nonzero
  previous/current leading diagonals, then applies the determinant-facing
  prefix-span self-norm `κ∞` route.  Two weak-component passes passed, so this
  counts as a listed dependency closure under visible triangular/nonzero-local
  diagonal, local condition-number, sign-choice, compact-update, and final
  solver-budget assumptions.  The remaining red QR bottleneck is deriving those
  assumptions from a computed-loop invariant, SVD/determinant-margin route, or
  explicitly keeping them as domain assumptions.
- Closed computed prefix-zero triangular self-norm route:
  `fl_householderStoredPanel_sequence_prefix_lower_zero` exposes the stored-loop
  prefix lower-zero induction, the local determinant adapters use only
  displayed leading-block triangular entries, and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_prefix_lower_zero_triangular_leading_blocks_kappaInf_selfNorm_budget`
  derives the determinant and completed-column lower-zero hypotheses from the
  stored recurrence itself.  Two weak-component passes passed, so this counts
  as a listed dependency closure for the computed-loop shape part of the red QR
  bottleneck.  It still leaves nonzero local diagonals, local condition-number
  bounds, sign choice, compact-update budgets, and final solver budgets
  visible.
- Closed signed-alpha specialization for the computed prefix-zero self-norm
  route with two weak-component passes:
  `signedHouseholderAlpha` is the explicit source-style Householder rule that
  chooses the sign opposite to the pivot, and the scalar lemmas
  `signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq` and
  `signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos` derive the
  Householder normalization and sign-choice hypotheses from that rule.  The QR
  wrapper
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_signed_alpha_trailingNorm_pos_sqrt_budget`
  and the solver wrappers
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_trailingNorm_pos_and_sqrt_budget`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_prefix_lower_zero_triangular_leading_blocks_kappaInf_selfNorm_budget`
  remove the independent sign-choice assumption whenever the stored loop
  exposes this concrete alpha definition.  Targeted/full builds, executable
  lookup, placeholder scan, whitespace check, axiom audit, PDF
  compile/repair/text extraction, and rendered page inspection all passed in
  two weak-component passes.  This closes the sign-choice listed
  dependency.
- Closed prefix-local previous diagonal nonbreakdown theorem with two
  weak-component passes:
  `fl_householderStoredPanel_sequence_prefix_diag_nonzero_of_step_diag_nonzero`
  proves that already written nonzero pivots stay nonzero at intermediate
  stored-loop prefixes, and
  `fl_householderStoredTrailingPanel_sequence_prefix_diag_nonzero_of_signed_alpha_trailingNorm_pos_sqrt_budget`
  supplies the signed-alpha trailing-loop version.  The solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget`
  uses those facts to remove previous local diagonal hypotheses from the
  computed prefix-zero self-norm certificate.  This narrows the nonzero-diagonal
  dependency to the current leading pivot, while local condition-number,
  compact-update, and final solver budgets remain visible.  The repeated audit
  passed targeted/full builds, executable lookup (rerun once after a concurrent
  build race), placeholder scan, whitespace check, axiom audit, PDF
  compile/repair/text extraction, and rendered page inspection.  This closes
  the previous-diagonal listed dependency; the red QR bottleneck is narrowed to
  current-pivot nonzero/nonbreakdown, local condition-number budgets,
  compact-update budgets, and final solver budgets.
- Closed explicit final Gram/RHS QR radii after the repeated weak-component
  audit:
  `qrSolveFinalDataPerturbationBudget` and
  `qrSolveFinalRhsPerturbationBudget` package the accumulated common-`Q`
  rectangular data/RHS radii plus the rounded top-block triangular-solve
  radius, while `qrSolveFinalGramBudget` and `qrSolveFinalRhsBudget` package
  the induced Gram-system radii.  The solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget`
  instantiates the final `hG`/`hg` hypotheses of the prefix-local route with
  those exact radii.  Two passes passed: targeted/full builds, executable
  lookup, placeholder scan, whitespace check, axiom audit, PDF
  compile/repair/text extraction, and rendered page inspection.  This closes
  the final Gram/RHS listed dependency; the red QR bottleneck is narrowed to
  current-pivot nonzero/nonbreakdown, local condition-number budgets,
  compact-update budgets, and square-root/compact pivot-budget derivations.
- Closed explicit compact-update QR budget after the repeated weak-component
  audit:
  `householderCompactRelativeBudget` and
  `householderCompactPanelRelativeBudget` package one-vector and one-panel
  compact-update relative radii, while
  `storedQRCompactStepRelativeBudget` and
  `storedQRCompactSequenceRelativeBudget` sum those radii over the stored QR
  sequence.  The solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget`
  chooses this displayed sequence budget as the compact-step constant and then
  reuses the explicit final Gram/RHS radii.  Two passes passed: targeted/full
  builds, executable lookup, placeholder scan, whitespace check, axiom audit,
  PDF compile/repair/text extraction, and rendered page inspection.  This
  closes the separate compact-update-domination listed dependency; the red QR
  bottleneck is narrowed to current-pivot nonzero/nonbreakdown, local
  condition-number budgets, and square-root/compact pivot-budget derivations.
- Closed positive trailing norm from the square-root compact budget after the
  repeated weak-component audit:
  `householderTrailingNorm2Sq_pos_of_nonneg_budget_lt_sqrt` proves that a
  nonnegative budget strictly below
  `sqrt (householderTrailingNorm2Sq n p x)` forces the trailing norm square to
  be positive.  The prefix-local explicit final-budget and explicit
  compact-budget solver wrappers now derive their positive-trailing-norm
  obligations internally from the square-root budget hypotheses.  Two passes
  passed: targeted/full builds, executable lookup, placeholder scan,
  whitespace check, axiom audit, PDF compile/repair/text extraction, and
  rendered page inspection.  This closes the separate positive-trailing-norm
  listed dependency; the red QR bottleneck is narrowed to current-pivot
  nonzero/nonbreakdown, local condition-number budgets, and square-root/compact
  pivot-budget derivations.
- Closed the direct norm-square-to-square-root pivot-budget bridge after the
  repeated weak-component audit:
  `budget_lt_sqrt_householderTrailingNorm2Sq_of_dim_mul_budget_sq_lt_trailingNorm2Sq`
  proves that the dimensioned compact margin
  `m * budget^2 < householderTrailingNorm2Sq m p x` directly supplies the
  square-root budget consumed by the stored QR nonbreakdown theorem.  The
  stored-loop norm-square route
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_trailingNorm2Sq_budget`
  now uses this direct bridge rather than an active-entry detour.  Two passes
  passed: targeted/full builds, executable lookup, placeholder scan, whitespace
  check, axiom audit, PDF compile/repair/text extraction, and rendered page
  inspection.  This closes the scalar square-root conversion listed
  dependency; the red QR bottleneck is narrowed to current-pivot
  nonzero/nonbreakdown, local condition-number budgets, and
  conditioning-to-norm-square compact pivot-budget derivations.
- Closed the solver-facing explicit compact QR certificate with norm-square
  pivot margins after the repeated weak-component audit:
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_normSqBudget`
  composes the direct scalar bridge with the latest explicit compact-update and
  final-radius LSQRSolve wrapper.  The theorem now consumes the dimensioned
  margin `m * budget_k^2 < ||A_k(k:m,k)||_2^2` directly instead of exposing the
  square-root pivot-budget inequality.  Two passes passed: targeted/full
  builds, executable lookup, placeholder scan, whitespace check, axiom audit,
  PDF compile/repair/text extraction, and rendered page inspection.  This
  closes the square-root-expression listed dependency of the latest explicit
  compact QR certificate; the red QR bottleneck is narrowed to current-pivot
  nonzero/nonbreakdown, local condition-number budgets, and deriving the
  norm-square pivot margins from a conditioning or computed-loop invariant.
- Ruled out the false "full rank alone gives the first unpivoted pivot" route
  after the repeated weak-component audit:
  `qrPivotCounterexample2_first_pivot_zero`,
  `qrPivotCounterexample2_det_ne_zero`, and
  `not_forall_det_ne_zero_implies_first_pivot_ne_zero` formalize the real
  `2 x 2` column-swap counterexample.  The matrix is nonsingular, but its
  first unpivoted pivot is zero.  Two passes passed: targeted/full builds,
  executable lookup, placeholder scan, whitespace check, axiom audit, PDF
  compile/repair/text extraction, and rendered page inspection.  This closes a
  listed route-elimination dependency, not the positive nonbreakdown theorem;
  the red QR bottleneck is narrowed to source-faithful pivoting/no-breakdown or
  structured invariants for current-pivot nonzero, local condition-number
  budgets, and deriving the norm-square pivot margins from conditioning or a
  computed-loop invariant.
- Strengthened the same route elimination at the exact leading-principal-minor
  level: `qrPivotCounterexample2_first_leadingBlock_det_zero` and
  `not_forall_det_ne_zero_implies_all_leading_blocks_det_ne_zero` prove that
  the nonsingular `2 x 2` column-swap matrix also has zero determinant in its
  first unpivoted `1 x 1` leading QR block.  This rules out replacing all
  per-pivot leading-block determinant hypotheses by whole-matrix nonsingularity
  or full rank alone.  Two weak-component passes validated this route
  elimination with full/targeted builds, lookup, placeholder scans, axiom
  audits, PDF text extraction, and rendered PDF inspection.
- Ruled out the false "positive trailing norm gives the current unpivoted
  pivot" route after the repeated weak-component audit:
  `householderTrailingPivotCounterexample2`,
  `householderTrailingPivotCounterexample2_pivot_zero`,
  `householderTrailingPivotCounterexample2_trailingNorm2Sq_pos`, and
  `not_forall_trailingNorm2Sq_pos_implies_pivot_ne_zero` formalize the two-entry
  active column `x = (0, 1)` at pivot `0`.  Its active trailing squared norm is
  positive, but the current pivot entry is zero.  Two passes passed: full
  `lake build`, executable lookup after rerunning past a concurrent-build race,
  touched-file placeholder scan, whitespace check, repeated axiom audit, PDF
  compile/text extraction, and rendered page inspection.  This closes a listed
  route-elimination dependency, not the positive pivot theorem; the red QR
  bottleneck is narrowed to pivoting, structured leading-block determinant or
  nonzero-diagonal assumptions, a stronger computed-loop invariant, and the
  remaining conditioning/compact-smallness dependencies.
- Closed the structured current-pivot route after the repeated weak-component
  audit:
  `diag_ne_zero_of_upper_triangular_det_ne_zero`,
  `qrLeadingBlock_current_pivot_ne_zero_of_local_upper_triangular_det_ne_zero`,
  `fl_householderStoredTrailingPanel_sequence_current_pivot_ne_zero_of_leadingBlock_det_ne_zero`,
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_normSqBudget`
  show that, in the stored no-pivot QR loop, the stored lower-zero shape makes
  the displayed local leading block upper triangular, so a nonzero determinant
  for that block implies the current pivot is nonzero and the latest compact
  QR certificate can consume local leading determinants instead of a bare
  current-pivot hypothesis.  Two passes passed: targeted/full builds,
  executable lookup, placeholder scan, whitespace check, axiom audit, PDF
  compile/repair/text extraction, and rendered page inspection.  This closes
  the structured current-pivot listed dependency.  The red QR bottleneck is now
  narrowed to local condition-number budgets and deriving the norm-square/dual
  compact pivot margins from conditioning or a computed-loop invariant.
- Closed the structured norm-square margin route from local leading blocks and
  `kappaInf`/dual budgets after the repeated weak-component audit:
  `qrPrefixSupportSpannedByPreviousColumns_of_leadingBlock_upper_det_ne_zero`
  derives the prefix-span invariant from stored lower-zero shape plus
  nonsingular local leading blocks, and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget`
  uses the determinant-facing `kappaInf` bridge and leading-dual norm theorem
  to derive the dimensioned norm-square compact pivot margin internally.  Two
  passes passed: targeted/full builds, executable lookup, placeholder scan,
  whitespace check, axiom audit, PDF compile/repair/text extraction, and
  rendered page inspection.  This closes the listed norm-square-margin
  derivation dependency for the structured local-leading-block route.  The red
  QR bottleneck is now narrowed to deriving or justifying the local `kappaInf`,
  `K_k`, and dual compact-budget assumptions from conditioning or a computed
  loop invariant.
- Closed the structured direct inverse-∞ budget route after the repeated
  weak-component audit:
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_invNorm_dualBudget`
  derives the latest explicit compact/final-radius `LSQRSolveBackwardError`
  certificate from stored lower-zero shape, nonsingular local leading blocks, a
  direct inverse-∞ budget
  `(k+1)||nonsingInv(S_k)||_∞^2 <= K_k`, and the dual compact-budget inequality
  `m * budget_k^2 < 1/K_k`.  Two passes passed: targeted/full builds,
  executable lookup, placeholder scan, whitespace check, axiom audit, PDF
  compile/repair/text extraction, and rendered page inspection.  This closes
  the listed dependency that removed local `kappaInf` hypotheses from the
  latest structured compact route.  The red QR bottleneck is now narrowed to
  deriving the direct inverse-∞ and dual compact-budget assumptions from
  diagonal dominance, conditioning, or a computed-loop invariant, or keeping
  those assumptions visibly as source/domain conditions.
- Closed the diagonal-dominant structured direct inverse-∞ route after the
  repeated weak-component audit:
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_dualBudget`
  composes the determinant-facing Higham triangular inverse estimate
  `triInv_infNorm_sq_budget_of_diagDominantUpper_det_ne_zero` with the latest
  structured direct inverse-budget certificate.  Under local diagonal
  dominance, `det S_k != 0`, and the diagonal-minimum budget, it derives the
  direct `(k+1)||nonsingInv(S_k)||_∞^2 <= K_k` hypothesis internally.  Two
  passes passed: targeted/full builds, executable lookup, placeholder scan,
  whitespace check, axiom audit, PDF compile/repair/text extraction, and
  rendered page inspection.  This closes the listed dependency that replaced a
  raw direct inverse-∞ assumption by an existing Higham triangular-domain
  bound.  The red QR bottleneck is now narrowed to deriving local diagonal
  dominance and the dual compact-budget inequality from conditioning or a
  computed-loop invariant, or keeping those assumptions visibly as
  source/domain conditions.
- Ruled out the false "upper triangular with nonzero diagonal implies
  diagonal dominance" route after the repeated weak-component audit:
  `diagDominanceCounterexample2_upper`,
  `diagDominanceCounterexample2_diag_nonzero`,
  `diagDominanceCounterexample2_not_diagDominant`, and
  `not_forall_upper_tri_diag_nonzero_implies_diagDominant` formalize the
  concrete `2 x 2` counterexample `[[1,2],[0,1]]`.  The matrix is upper
  triangular and has nonzero diagonal entries, but it is not diagonally
  dominant.  Two passes passed: targeted/full builds, executable lookup,
  placeholder scan, whitespace check, axiom audit, PDF compile/repair/text
  extraction, and rendered page inspection.  This closes a listed route
  elimination, not the positive diagonal-dominance theorem.  The red QR
  bottleneck is now narrowed to deriving local diagonal dominance from a
  stronger computed-loop/conditioning invariant, deriving the dual
  compact-budget inequality, or keeping those assumptions visibly as
  source/domain conditions.
- Closed the concrete-dual diagonal-dominant compact QR dependency after the
  repeated weak-component audit:
  `diagDominantUpperInvBudgetExpr`,
  `diagDominantUpperInvBudgetExpr_pos`,
  `triInv_infNorm_sq_budget_of_diagDominantUpper_det_ne_zero_twice_budget`, and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualBudget`
  choose `K_k = 2D_k` internally, where `D_k` is the formal Higham
  diagonal-dominant inverse budget.  The latest diagonal-dominant route no
  longer has an arbitrary auxiliary `K_k`; it assumes the direct compact
  smallness condition `m * budget_k^2 < 1/(2D_k)`.  Two passes passed:
  targeted/full builds, executable lookup, placeholder scan, whitespace check,
  axiom audit, PDF compile/repair/text extraction, and rendered page
  inspection.  The red QR bottleneck is now narrowed to deriving local diagonal
  dominance and the direct compact smallness condition from a stronger
  computed-loop/conditioning invariant, or keeping those assumptions visibly as
  source/domain conditions.
- Closed the product-form concrete-dual compact QR dependency after the
  repeated weak-component audit:
  `mul_sq_lt_inv_two_mul_of_two_mul_mul_sq_lt_one` and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualProductBudget`
  replace the denominator-shaped compact-smallness assumption
  `m * budget_k^2 < 1/(2D_k)` by the dimensionless product condition
  `2D_k * (m * budget_k^2) < 1`, deriving denominator positivity from the same
  diagonal-dominant inverse-budget positivity theorem.  Two passes passed:
  targeted/full builds, executable lookup, placeholder scan, whitespace check,
  axiom audit, PDF compile/repair/text extraction, and rendered page
  inspection.  The red QR bottleneck is now narrowed to deriving local diagonal
  dominance and this product compact-smallness condition from a stronger
  conditioning/computed-loop invariant, ruling out a listed route, or keeping
  those assumptions visibly as source/domain conditions.
- Chose and closed the Higham columnwise final-factorization route after the
  proof-source checkpoint:
  `fl_householderStoredTrailingPanel_higham_columnwise_factorization`
  combines the stored trailing Householder columnwise perturbation theorem with
  the stored top-block shape theorem.  It yields one orthogonal `Q`,
  perturbations `DeltaA` and `Deltab`, columnwise/RHS geometric perturbation
  bounds, the final stored `[R;0]` shape, top transformed RHS, and
  upper-triangular `R`.  This is the source-faithful positive factorization
  assembly for Higham's columnwise theorem.  It does not close the
  solver/preconditioner theorem, because nonzero diagonal, conditioning or
  inverse-budget bounds, and compact-smallness/product-budget assumptions remain
  separate obligations.
- Modularity cleanup: the stored-loop solver handoff
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget`
  now reuses
  `fl_householderStoredTrailingPanel_higham_columnwise_factorization` directly
  instead of rebuilding the perturbation sequence and shape facts.  It now has
  two weak-component passes: targeted/full builds, lookup execution, placeholder
  scan, diff check, axiom audit, PDF compile/text extraction, and rendered page
  inspection.  This keeps the library layered, but it does not discharge the
  remaining nonzero diagonal, conditioning, or product-smallness obligations.
- User chose route 1, the stronger computed-loop/off-diagonal-control route.
  The first positive step is now formalized as
  `StoredQROffDiagonalControlInvariant` and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_offDiagonalControl`.
  This closes the packaging/consumption dependency: one named invariant now
  supplies local leading-block nonsingularity, local diagonal dominance, and
  stored-sequence compact-product smallness to the existing solver certificate.
  Two weak-component passes validated the wrapper, lookup, axiom audit, PDF
  text, and rendered page.  It does not prove the invariant from ordinary
  no-pivot QR.  The red
  bottleneck is therefore reduced to a smaller dependency: prove
  `StoredQROffDiagonalControlInvariant` from a source-specific
  off-diagonal-control, pivoting, or ordering assumption, or keep the invariant
  visible as the theorem's domain hypothesis.
- The route-1 dependency has been reduced one step further by the
  source-shaped theorem family
  `StoredQRSourceOffDiagonalControl`,
  `StoredQROffDiagonalControlInvariant.of_sourceOffDiagonalControl`, and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl`.
  The packaged determinant and diagonal-dominance fields are no longer the
  primitive target: they are derived from local upper-triangular shape,
  nonzero local diagonals, and row-wise off-diagonal domination.  The remaining
  red-bottleneck dependency is now to prove `StoredQRSourceOffDiagonalControl`
  from source-specific pivoting, ordering, or off-diagonal-growth assumptions,
  or keep that source-shaped control data visible as the domain condition.
  Two weak-component passes validated the source-shaped wrapper, lookup entry,
  axiom audit, theorem PDF text, and rendered pages 128--129.
- Local library reuse has removed the triangular-shape field from the remaining
  source-specific burden.  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diag_offdiag_product`
  applies the existing stored Householder prefix-lower-zero theorem to derive
  upper-triangular displayed leading blocks from the recurrence.  The active
  red-bottleneck dependency is now strictly the three remaining obligations:
  nonzero displayed diagonals, row-wise off-diagonal domination, and
  compact-product smallness.  Two weak-component passes validated this
  triangular-source reduction, including full build, executable lookup, diff
  check, placeholder scan, axiom audit, PDF compile/text extraction, and
  rendered page inspection.
- Local library reuse has also reduced the nonzero-displayed-diagonal
  obligation.  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_pivot_sqrtBudget_offdiag_product`
  uses the existing signed-alpha stored prefix-diagonal theorem to derive all
  previously written diagonal entries from the stored loop and square-root
  nonbreakdown budget.  The active red-bottleneck dependency is now strictly:
  current pivot nonzero, square-root nonbreakdown budget, row-wise
  off-diagonal domination, and compact-product smallness.  Two weak-component
  passes validated this reduction, including full build, executable lookup,
  diff check, placeholder scan, axiom audit, PDF compile/text extraction, and
  rendered page inspection.
- Local library reuse has reduced the raw current-pivot field to local
  leading-block nonsingularity.
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_sqrtBudget_offdiag_product`
  uses the stored lower-zero determinant bridge to derive the current pivot
  from `det S_k != 0`.  Two weak-component passes validated this reduction.
- Local library reuse has also reduced the square-root budget field to the
  norm-square margin already used by the QR library.
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_offdiag_product`
  applies
  `budget_lt_sqrt_householderTrailingNorm2Sq_of_dim_mul_budget_sq_lt_trailingNorm2Sq`
  and then reuses the determinant-shaped source theorem.  The active
  red-bottleneck dependency is now strictly: local leading-block
  nonsingularity, norm-square nonbreakdown margin, row-wise off-diagonal
  domination, and compact-product smallness.  Two weak-component passes now
  validate this norm-square reduction.
- Route-choice checkpoint: local search found no existing theorem that derives
  those four residual source fields from the ordinary unpivoted stored
  Householder recurrence.  The existing counterexample rows already rule out
  the tempting shortcuts from full rank, determinant nonzero, positive trailing
  norm, exact QR shape, finite conditioning, diagonal dominance alone, product
  smallness alone, and the exact no-pivot recurrence.  Further progress now
  requires a mathematical theorem-family choice: keep these fields as visible
  source/domain assumptions, change the algorithm to a pivoted/sorted or
  off-diagonal-controlled QR theorem family, or provide a source/application
  class that proves them.
- Current scoping choice for the existing unpivoted theorem family: keep the
  four residual fields visible.  This closes the route-choice bookkeeping for
  the implemented conditional theorem family, but it does not close the generic
  paper-level QR/preconditioner item.  Adjacent unpivoted QR adapters remain
  frozen; future progress must change the algorithmic theorem family or prove
  the four fields from an explicit source/application class.
- Route switch now selected for the positive QR work: the no-pivot route is
  frozen at the four visible source fields above, and the active positive route
  is Cox--Higham's pivoted/sorted weighted least-squares Householder QR theorem
  family.  External source acquisition recorded that ordinary unpivoted
  Householder QR is not row-wise stable for weighted least-squares data, while
  column pivoting together with row pivoting or initial row sorting and the
  standard sign convention is the source-backed route.  First dependency
  closure: `householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_of_mul_nonpos`
  and `householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_signed`
  prove the Cox--Higham Lemma 2.1 / equation (2.5) denominator lower bound
  `2 ||x_tail||_2^2 <= v^T v`; two weak-component passes validate this
  closure.  The next dependency now also has two weak-component passes:
  `householderTrailingColumnNorm2Sq`,
  `exists_householderTrailingColumnNorm2Sq_active_max`,
  `abs_inner_householderTrailingActiveVector_trailingPart_le_vecNorm2_mul_sqrt`,
  and
  `abs_inner_householderTrailingActiveVector_column_le_vecNorm2_mul_sqrt_of_pivot_max`
  formalize finite active-column pivot selection and the Cauchy--Schwarz
  comparison `|v^T y_tail| <= ||v||_2 ||x_tail||_2`.  The next scalar
  dependency has two weak-component passes:
  `abs_householderBeta_mul_inner_column_le_sqrt_two_of_signed_pivot_max`
  gives the Cox--Higham Lemma 2.1 endpoint `|beta*v^T y_tail| <= sqrt 2`,
  and
  `abs_householder_signed_pivot_update_entry_le_one_add_sqrt_two_mul_row_bound`
  gives the equation (4.3) one-step row-entry growth estimate.  The row-sorting
  stage accumulation is now locally formalized by
  `scalar_growth_iterate_bound`,
  `coxHigham_rowSorting_active_entry_bound_of_prior_growth`, and
  `coxHigham_rowSorting_active_entry_bound_of_stage_growth`; two
  weak-component passes validate this dependency.  The pivot-row active-tail
  norm step from Cox--Higham equations (4.4)--(4.5) is now formalized in
  ambient-dimension form by `vecNorm2_le_sqrt_card_mul_of_abs_le`,
  `coxHigham_pivot_row_entry_bound_of_active_tail_entry_bound`, and
  `coxHigham_pivot_row_entry_bound_of_stage_entry_bound`; two weak-component
  passes validate this dependency.  The scalar row-wise
  accumulated perturbation dependency is now locally formalized by
  `scalarAffineGrowthBudget`, `scalar_affine_growth_iterate_bound`,
  `coxHigham_rowwise_error_accumulation_bound`, and
  `coxHigham_rowSorting_active_entry_bound_with_accumulated_error`; two
  weak-component passes validate this dependency.  The concrete stored rounded
  panel per-step FP budget is now represented by
  `fl_householderStoredPanelStep_active_entry_componentwise_error_bound`,
  `coxHigham_storedPanelStep_row_error_recurrence_of_exact_lipschitz`, and
  `coxHigham_storedPanel_sequence_rowwise_error_accumulation_bound_of_exact_lipschitz`;
  two weak-component passes validate this dependency as a scoped FP budget
  instantiation, not as the final row-wise QR theorem.  The cleaner direct
  row-magnitude adapter is now also formalized by
  `coxHigham_storedPanelStep_active_entry_bound_of_exact_growth` and
  `coxHigham_storedPanel_sequence_active_entry_bound_of_exact_growth`;
  two weak-component passes validate this route-shape correction as a scoped
  dependency, not as the final row-wise QR theorem.
  The non-pivot active-row exact same-reflector bridge is now formalized by
  `matMulVec_householder_signed_pivot_update_entry_eq` and
  `coxHigham_exact_same_reflector_row_growth_of_signed_pivot_row_bound`; two
  weak-component passes validate this one-step bridge as a scoped route
  dependency, not as the final row-wise QR theorem.
  The exact signed pivot-row same-reflector bridge is also now formalized by
  `householderBeta_mul_inner_self_eq_two`,
  `abs_matMulVec_householder_pivot_le_trailing_vecNorm2_of_zero_prefix_orthogonal`,
  `coxHigham_signed_pivot_row_update_abs_le_trailing_vecNorm2`, and
  `coxHigham_exact_signed_pivot_row_entry_bound_of_stage_entry_bound`; two
  weak-component passes validate this one-step pivot-row bridge as a scoped
  route dependency, not as the final row-wise QR theorem.
  The one-step active-row case split is now formalized by
  `coxHigham_exact_signed_pivot_active_row_entry_bound_of_stage_bounds`; two
  weak-component passes validate this combined one-step bridge as a scoped
  route dependency, not as the final row-wise QR theorem.
  The exact multi-stage loop bridge is now represented by the concrete
  `exactSignedPivotHouseholderPanelStep` and the sequence theorems
  `coxHigham_exactSignedPivotPanel_sequence_active_entry_bound_of_stage_budgets`
  and
  `coxHigham_exactSignedPivotPanel_sequence_active_entry_bound_of_geometric_stage_budgets`;
  two weak-component passes validate this stage-budget propagation dependency as
  a scoped exact loop theorem, not as the final row-wise QR theorem.  The
  exact-to-FP handoff for this honest active-row factor is now represented by
  `coxHigham_storedPanelStep_active_entry_bound_of_exact_growth_factor`,
  `coxHigham_storedPanel_sequence_active_entry_bound_of_exact_growth_factor`,
  and
  `coxHigham_storedPanel_sequence_active_entry_bound_of_exact_active_growth`;
  two weak-component passes validate this handoff dependency as a scoped
  exact-to-FP bridge, not as the final row-wise QR theorem.
  The source-shaped handoff has also been corrected to a visible-stage-budget
  theorem family:
  `coxHigham_storedPanelStep_active_entry_bound_of_exact_stage_budget_factor`,
  `coxHigham_storedPanel_sequence_active_entry_bound_of_exact_stage_budgets_factor`,
  `coxHigham_storedPanel_sequence_active_entry_bound_of_exact_active_stage_budgets`,
  and
  `coxHigham_storedPanelStep_active_entry_bound_of_signed_pivot_stage_bounds`;
  two weak-component passes validate this stage-budget dependency as a scoped
  exact-to-FP bridge, not as the sorting-policy proof or final row-wise QR
  theorem.
  The next one-step sorting-field adapter is now added but not yet fully
  audited: `coxHigham_exactSignedPivotPanelStep_active_block_bound_of_stage_bound`
  shows that a single active-block bound supplies the separate row and column
  stage fields of the signed-pivot one-step theorem.  Its first weak-component
  pass is clean; the second pass is pending.
  The second weak-component pass is now also clean, so this adapter is a scoped
  closed dependency.  It still does not prove multi-stage active-block
  propagation.
  The exact sequence now has active-block stage-budget wrappers,
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_stage_budgets`
  and
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_geometric_stage_budgets`;
  two weak-component passes validate these wrappers as scoped dependencies, not
  as the concrete sorting-policy proof or final QR/preconditioner theorem.
  The next exact active-block propagation theorem
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound`
  now has two weak-component passes clean. It proves the active-block budget
  family from an initial entrywise bound and monotone active windows, while
  keeping positive active norm and pivot-max fields visible.
  The positive active-norm field is now reduced by
  `householderTrailingColumnNorm2Sq_pos_of_pivot_max_exists_active_entry_ne`
  and
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_block_nonzero`:
  pivot maximality plus a nonzero entry in the remaining active block gives
  the positive pivot-column active norm. Two weak-component passes validate
  this reduction as a scoped dependency. The raw pivot-max field is now supplied
  by the finite active max-pivot selector and the sequence wrapper
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_max_pivot`,
  replacing the inequality by a concrete pivot-policy equation; two
  weak-component passes validate this reduction as a scoped dependency. The
  nonzero-active-block witness is now reduced further to positive active-block
  mass via `householderActiveBlockNorm2Sq`,
  `exists_active_entry_ne_of_householderActiveBlockNorm2Sq_pos`, and
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_block_norm_pos`.
  Two weak-component passes validate this positive-mass bridge as a scoped
  dependency. The active max-pivot policy for displayed sorted stages is now
  supplied by the column-swap theorem
  `householderSwapColumns_activeMaxPivotColumn_pivot_max` and the sequence
  wrapper
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_swapped_active_max_pivot`.
  Two weak-component passes validate this swapped-policy bridge as a scoped
  dependency.
  The raw-stage mass bridge is now validated:
  `householderActiveBlockNorm2Sq_pos_of_exists_active_entry_ne` proves that a
  concrete nonzero active entry gives positive active-block squared mass,
  `householderActiveBlockNorm2Sq_swapColumns_pos_of_pos` proves that a column
  swap inside the active suffix preserves positivity of this mass, and
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_swapped_active_max_pivot_of_raw_active_block_norm_pos`
  feeds raw pre-swap mass into the exact swapped-stage active-block sequence.
  Two weak-component passes validate this raw-to-swapped mass bridge as a
  scoped dependency.  The rounded active-block stored-panel propagation theorem
  has now been added but not yet fully audited:
  `signedPivotHouseholderVector` and `signedPivotHouseholderBeta` package the
  concrete signed-pivot reflector fields, and
  `coxHigham_storedPanel_sequence_active_block_bound_of_signed_pivot_stage_bounds`
  propagates rounded active-block budgets through the stored compact panel
  update under visible positive pivot norm, pivot-maximality, completed-column
  and pivot-column storage equations, monotone active windows, and compact FP
  budget recurrence.  Two weak-component passes validate this rounded
  active-block recurrence as a scoped dependency.  The positive raw-stage
  active-block mass field is now connected to the existing QR rank/determinant
  nonbreakdown infrastructure by
  `householderActiveBlockNorm2Sq_pos_sequence_of_leading_block_det_ne_zero`,
  and two weak-component passes validate that scoped dependency.  A new
  route-elimination theorem,
  `not_forall_leadingBlock_upper_det_activeBlockPos_implies_offdiag_le_diag`,
  rules out the shortcut from upper-triangular nonsingular leading blocks plus
  positive active-block mass to the solver-side row-wise off-diagonal
  domination field.  This is red-bottleneck progress because it removes a
  listed false route: off-diagonal control must be proved from a stronger
  pivoting/ordering/growth invariant or kept visible.  Next listed
  dependencies are supplying the determinant/lower-zero and off-diagonal
  fields for the concrete raw stages and connecting the rounded sequence
  result to the QR/preconditioner solve theorem, possibly while keeping
  raw-stage nonbreakdown and signed-pivot storage fields explicit.
  The row-sorting side of the Cox--Higham route now has a local
  permutation-invariance foundation: `vecPermute`, `rectPermuteRows`,
  `rectPermuteCols`, `vecNorm2Sq_permute`, `frobNormSqRect_permuteRows`,
  `frobNormSqRect_permuteCols`, `frobNormRect_permuteRows`,
  `frobNormRect_permuteCols`, `rectMatMulVec_permuteRows`,
  `rectLSGram_permuteRows`, `rectLSRhs_permuteRows`,
  `lsResidual_permuteRows`, and `lsObjective_permuteRows`.  This closes the
  row-sorting objective/normal-equation invariance dependency only.  The
  matching column-pivot bookkeeping is now added too:
  `vecPermute_symm_vecPermute`, `vecPermute_vecPermute_symm`,
  `rectMatMulVec_permuteCols`, `rectLSGram_permuteCols`,
  `rectLSRhs_permuteCols`, `RectLSNormalEquations.of_permuteCols`,
  `lsResidual_permuteCols`, `lsObjective_permuteCols`, and
  `IsLeastSquaresMinimizer.of_permuteCols`.  This closes the coefficient
  relabeling/objective/normal-equation dependency only.  The combined
  row-sorting/column-pivot bridge is now local as well:
  `rectLSGram_permuteRowsCols`, `rectLSRhs_permuteRowsCols`,
  `RectLSNormalEquations.of_permuteRowsCols`, `lsResidual_permuteRowsCols`,
  `lsObjective_permuteRowsCols`, and
  `IsLeastSquaresMinimizer.of_permuteRowsCols` pull a row-sorted and
  column-pivoted normal-equation solution or exact minimizer back to the
  original coordinates in one step.  This still closes bookkeeping only; the
  concrete pivoted/sorted Householder growth/sorting and diagonal lower-bound
  fields remain the active red dependency.  The unpivoted
  source-controlled solve connection is now also formalized:
  `storedQRFinalR`, `storedQRFinalTopRhs`, `storedQRBackSubSolution`, and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver`
  compose the stored-QR `LSQRSolveBackwardError` theorem into the equation (8)
  high-probability rounded sampled-row objective theorem once
  `StoredQRSourceOffDiagonalControl` is supplied.  This closes the solver
  handoff under explicit source-control fields.  The remaining bottleneck
  dependencies are proving those fields for a concrete sorted/pivoted rounded
  loop, or replacing them with a proved source-backed growth invariant.
  The latest dependency closure decomposes the row-wise off-diagonal field:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product`
  show that it is enough to supply a Cox--Higham-style row-growth upper budget
  for each displayed upper entry and a matching lower bound by the displayed
  diagonal magnitude.  Two weak-component passes validate this decomposition
  as a scoped dependency.  This is direct red-bottleneck progress because it
  splits the remaining off-diagonal-control obligation into two listed
  dependencies: row-growth budget propagation and diagonal lower-bound
  nonbreakdown.
  The row-growth propagation dependency now has a QR-layer bridge:
  `qrLeadingOffdiagStop`,
  `fl_householderStoredPanel_sequence_completed_column_eq_pivot_succ`, and
  `fl_householderStoredPanel_sequence_leadingBlock_offdiag_budget_of_exact_stage_budgets_factor`
  convert per-entry Cox--Higham stage budgets and compact-budget absorption
  into the displayed leading-block upper off-diagonal `rowBudget` field.
  Two weak-component passes validate this row-growth propagation bridge as a
  scoped dependency.  The least-squares layer now also has the direct
  source-control handoff:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_stageBudget_rowBudget_product`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_stageBudget_rowBudget_product`
  compose those stage budgets with explicit diagonal lower bounds into the
  local `LSQRSolveBackwardError` certificate.  Two weak-component passes
  validate this handoff as a scoped dependency.  The remaining listed
  dependencies are instantiating the concrete stage-budget/pivot-zeroing
  fields for the chosen pivoted/sorted loop and proving the matching diagonal
  lower-bound nonbreakdown field.  The row-growth bridge has now been narrowed
  to the concrete signed-stage loop by `storedQRSignedStageVector`,
  `storedQRSignedStageBeta`, and
  `fl_householderStoredPanel_sequence_leadingBlock_offdiag_budget_of_signed_stage_budgets_factor`;
  focused build and two weak-component passes validate this specialization.
  The least-squares layer now also has the signed-stage handoff
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product`;
  focused build and two weak-component passes validate this handoff.  The
  pivot-column zeroing field is now closed by
  `storedQRSignedStage_pivot_column_zero_below_of_trailingNorm_pos` and
  `storedQRSignedStage_pivot_zeroing_field_of_trailingNorm_pos`; focused build
  and two weak-component passes validate this field.
  The norm-square-budget adapter
  `storedQRSignedStage_pivot_zeroing_field_of_normSqBudget`, together with
  the least-squares handoffs
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_normSqBudget`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_normSqBudget`,
  now removes the independent `hpivot` hypothesis from the signed-stage
  solver-facing route; focused build and two weak-component passes validate
  the adapter.
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
  active-row Cox--Higham branch for one concrete signed stored-QR stage.  Two
  weak-component passes now validate this scoped prefix/active dependency.
  The least-squares layer now has the uniform-stage-budget handoffs
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_stage_entry_bounds`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_stage_entry_bounds`;
  focused build validates that they derive the abstract exact-reflector field
  from concrete stage row/column entry bounds, pivot maximality, and
  norm-square nonbreakdown.  Two weak-component passes now validate this scoped
  exact-field handoff.
  The row-budget diagonal-lower-bound statement is now corrected by
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product_of_offdiag_rows`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product_of_offdiag_rows`:
  the comparison `rowBudget k i <= |S_k ii|` is required only for rows
  `i.val < k`, because row `i = k` has no strict upper off-diagonal entry.
  Focused build and two weak-component passes validate this theorem-statement
  correction.  The remaining listed dependencies are the concrete row-growth
  budgets, diagonal lower-bound/nonbreakdown for rows `i < k`, stage
  recurrence, determinant/norm-square nonbreakdown, compact-product smallness,
  and final QR/preconditioner theorem.
  The same offdiag-row-only correction is now propagated through the stage and
  signed-stage handoffs:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_stageBudget_rowBudget_product_of_offdiag_rows`,
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_stageBudget_rowBudget_product_of_offdiag_rows`,
  the signed-stage and norm-square-derived pivot-zeroing `_offdiag_rows`
  variants, and the uniform-stage/stage-entry-bound `_offdiag_rows` variants.
  Focused `lake build LeanFpAnalysis.FP.Algorithms.LeastSquares.LSQRSolve`
  passes with only pre-existing `HouseholderQR.lean` warnings.  Two
  weak-component passes now validate this statement-correction propagation.
  The next statement correction is now added but not yet fully weak-checked:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_stage_entry_bounds_offdiag_rows`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_stage_entry_bounds_offdiag_rows`
  split the remaining stage entry hypotheses into one active-suffix block
  budget plus a prefix displayed-row budget.  Focused LSQRSolve build passes.
  This reduced the bottleneck to active-suffix recurrence, prefix-row bound,
  diagonal lower bounds for rows `i < k`, determinant/norm-square
  nonbreakdown, compact-product smallness, and the final QR/preconditioner
  theorem.  Two weak-component passes now validate this active/prefix
  statement-correction dependency.  The active-suffix recurrence handoff has
  now also been added:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_offdiag_rows`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_offdiag_rows`
  instantiate the local Cox--Higham active-block sequence theorem for the
  signed stored-QR pivot map.  Focused LSQRSolve build passes, and two
  weak-component passes now validate this dependency closure.  This closes the
  raw active-block-bound field only; the prefix-row bound, diagonal lower
  bounds, determinant/norm-square nonbreakdown, compact-product smallness, and
  final QR/preconditioner theorem remain open.
  The prefix displayed-row field has now been reduced to a one-step recurrence:
  `storedQRSignedStage_active_block_bound_of_signed_stage_budget` factors the
  active-block recurrence into a reusable theorem, and
  `storedQRSignedStage_prefix_row_bound_of_active_block_and_prefix_budget`
  proves prefix-row stage bounds by induction from that active-block theorem,
  the signed-stage exact same-reflector split, and a prefix compact-update
  budget.  The source-control and solver wrappers
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_prefixRowRecurrence_offdiag_rows`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_prefixRowRecurrence_offdiag_rows`
  remove the raw prefix-row-bound hypothesis.  Focused LSQRSolve build passes.
  Two weak-component passes now validate this prefix-row recurrence handoff.
  The one-step budget fields have now been packaged by a finite global
  compact-step budget:
  `storedQRSignedStageGlobalCompactBudget`,
  `storedQRSignedStage_active_prefix_budgets_of_globalCompactBudget`, and the
  `_activePrefix_activeBlockRecurrence_globalCompactBudget_offdiag_rows`
  source-control/solver wrappers derive the displayed off-diagonal,
  active-block, and prefix-row one-step inequalities from a single scalar
  recurrence `Γ_m B_t + Δ_t^max <= B_{t+1}`.  Focused LSQRSolve build passes;
  two weak-component passes now validate this finite-global-budget handoff as a
  scoped dependency closure.  The same recurrence now also supplies the
  stage-horizon monotonicity bridge:
  `storedQRSignedStageGlobalCompactBudget_nonneg` and
  `storedQRSignedStageBudget_mono_on_stages_of_globalCompactBudget` prove that
  nonnegative stage budgets are monotone whenever `a <= b <= n`, without
  asserting anything about indices beyond the QR horizon.  The new
  `qrStageHorizonBudget` helper and the `_of_horizonBudget`
  completed-column global-product source-control/solver wrappers clamp the
  budget after `n`, so the old globally monotone theorem surfaces can be reused
  without a separate global monotonicity hypothesis.  The completed-column
  field is now also derived
  by `storedQRSignedStage_completed_column_preservation`, using the stored
  lower-zero invariant and zero-prefix Householder support; the corresponding
  source-control and solver wrappers remove the explicit completed-column
  hypothesis from this route.  Two weak-component passes are clean for that
  handoff.  The per-pivot compact-product field is now packaged by
  `storedQRCompactSequenceProductBudget` and the
  `_globalCompactBudget_completedColumns_globalProduct_offdiag_rows` wrappers;
  two weak-component passes are clean for this handoff.  The equation (8)
  assembly under these visible active/prefix assumptions is now present as
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_solver`;
  two weak-component passes are clean for that assembly theorem.  Its
  horizon-clamped sibling
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_solver_of_horizonBudget`
  now removes the samplewise global budget-monotonicity field by applying the
  LS.2g-hx source-control wrapper to each sample trace.  The matching
  `κ∞`/dual-budget sibling
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_kappaInf_dualBudget_solver_of_horizonBudget`
  derives norm-square nonbreakdown and uses the same horizon-clamped base
  wrapper.  The active-pivot horizon sibling
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver_of_horizonBudget`
  first recovers raw pivot maximality from the finite active selector and then
  calls that LS.2g-hz wrapper, so the active-pivot probability route also no
  longer exposes samplewise global budget monotonicity.  The visible row-max
  horizon sibling
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_horizonBudget`
  derives the diagonal lower-bound family from the row-max scalar defect and
  displayed-row comparison, then calls the active-pivot horizon theorem, so the
  row-max probability surface also drops the samplewise global monotonicity
  field.  Its actual-unit horizon sibling derives the sampled validity fields
  from `(s : ℝ) * fp.u < 1` and calls that row-max horizon theorem, removing
  both sampled `gammaValid` fields and global monotonicity from the visible
  row-max actual-unit surface.  Full validation is clean for the horizon
  probability wrappers, including that actual-unit horizon sibling:
  focused RandNLA least-squares build, executable lookup, standard-only axiom
  audit, two theorem-PDF compiles (latest actual-unit horizon compile to 272
  pages), whole-PDF text extraction, rendered inspection of pages 227, 228,
  229, 230, 265, and 269, broad `lake build`, whitespace check, marker scan,
  and temporary-file cleanup all passed.  The
  red bottleneck is now reduced to proving diagonal-lower or row-max/comparison
  fields, determinant/norm-square nonbreakdown, and global compact-product
  smallness for a concrete pivoted/sorted loop, or explicitly keeping these
  fields as source/domain assumptions.
  The finite global-product smallness packaging has now been sharpened in the
  reverse direction: `storedQRCompactSequenceProductBudget_lt_one_of_forall_expr_lt`
  and `storedQRCompactSequenceProductBudget_lt_one_of_forall_pivot_product`
  prove that the scalar condition `storedQRCompactSequenceProductBudget < 1`
  follows from the finite family of per-pivot product inequalities.  This is a
  listed dependency closure for the bookkeeping part of global-product
  smallness, not a proof of the per-pivot inequalities themselves.  Two
  weak-component passes are clean.  The remaining red-bottleneck work is to
  derive the per-pivot compact-product inequalities, offdiag-row diagonal lower
  bounds, and local determinant/norm-square nonbreakdown from a concrete
  pivoted/sorted loop, or keep those fields visible as source/domain
  assumptions.
  The norm-square nonbreakdown branch has now been reused in the active/prefix
  global-product route:
  `storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget`
  derives the dimensioned pivot margin from local leading-block determinant,
  `κ∞`/self-norm, and dual compact-budget data, and the corresponding
  `kappaInf_dualBudget` source-control, solver, and equation (8) wrappers
  thread that adapter through the newest global-product assembly.  Focused
  builds, lookup, marker scan, qualified axiom audit, PDF compile, text
  extraction, and rendered-page inspection now give two weak-component passes.
  This removes the raw norm-square field from that route when the structured
  local conditioning budgets are supplied.  The remaining red-bottleneck work
  is offdiag-row diagonal lower bounds, proving/justifying the local
  leading-block determinant and `κ∞`/dual compact-budget fields for a concrete
  loop, and deriving the per-pivot/global product smallness from that loop.
  A diagonal-dominant global-product branch is now added:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_diagDominant_globalProduct`,
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_globalProduct`,
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_globalProduct`,
  and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_globalProduct_kappaInf_dualBudget_solver`.
  This is progress on the listed offdiag-row diagonal lower-bound dependency:
  if each local leading block is explicitly `IsDiagDominantUpper`, the
  diagonal lower-bound field is supplied by the local diagonal-dominance
  infrastructure.  It deliberately keeps diagonal dominance, local
  determinant/conditioning budgets, and global product smallness visible rather
  than pretending that the no-pivot QR loop proves them.  Two weak-component
  passes are clean for this diagonal-dominant branch.
  The product-smallness route is now reduced one level further by
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_factor_norm_bounds`:
  global bounds `Dmax` and `Nmax` plus the scalar inequality
  `2 * Dmax * (m * (c_seq * Nmax)^2) < 1` imply
  `storedQRCompactSequenceProductBudget < 1`.  This is a listed dependency
  closure for scalarizing the product condition; it does not prove those global
  bounds or the scalar inequality from the computed loop.  Two weak-component
  passes are clean for this scalar adapter.  The remaining red dependencies are
  concrete-loop proofs or route classifications for diagonal dominance, local
  determinant/conditioning budgets, the global factor/norm bounds, and the
  scalar smallness inequality.
  The global factor/norm bounds are now also canonicalized by
  `storedQRDiagDominantInvFactorBudget`, `storedQRPivotColumnNormBudget`, and
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_smallness`.
  Two weak-component passes are clean for this finite-max adapter.  The product
  side of the red bottleneck is therefore narrowed to proving the scalar
  smallness inequality for those canonical maxima, still under local diagonal
  dominance.
  Route-1 finite-max handoff progress: the canonical scalar inequality has now
  been threaded through the main diagonal-dominant QR surfaces by
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_diagDominant_finiteMaxSmallness`,
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_finiteMaxSmallness`,
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_finiteMaxSmallness`, and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_kappaInf_dualBudget_solver`.
  This directly closes a listed dependency in the theorem surface: the
  diagonal-dominant equation (8) branch no longer exposes the raw
  `storedQRCompactSequenceProductBudget < 1` field when the canonical
  finite-max scalar inequality is supplied.  The remaining red dependencies are
  still local diagonal dominance, local leading-block determinant/conditioning
  and dual compact-budget fields, and proving the canonical scalar smallness
  inequality from a concrete computed-loop/off-diagonal-control invariant.
  Two weak-component passes are clean: focused build, executable lookup,
  `git diff --check`, marker scan, qualified axiom audit, PDF compile, text
  extraction, and rendered page inspection.  The axiom audit reports only
  standard `propext`, `Classical.choice`, and `Quot.sound`.

  Route-1 concrete-dual finite-max handoff progress: the finite-max
  diagonal-dominant branch now has direct solver and equation (8) wrappers,
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_diagDominant_finiteMaxSmallness_concreteDual`
  and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_concreteDual_solver`.
  This directly closes the listed dependency for removing auxiliary `κ`, `K`,
  and dual compact-budget fields from the finite-max diagonal-dominant equation
  (8) surface.  The remaining red dependencies on this route are proving or
  classifying local diagonal dominance, local leading-block determinant
  nonzeroness, and the canonical finite-max scalar smallness inequality for a
  concrete no-pivot stored QR loop.  First weak-component validation is clean:
  focused build, executable lookup, `git diff --check`, touched-file marker
  scan, qualified axiom audit, PDF compile, text extraction, and rendered-page
  inspection all passed.  The axiom audit reports only standard `propext`,
  `Classical.choice`, and `Quot.sound`.  The repeated pass is also clean, and
  the temporary axiom-audit file was deleted.  This checkpoint now has two
  consecutive clean passes.

  Route-1 determinant-free concrete-dual handoff progress: the local
  determinant field has been closed inside the diagonal-dominant finite-max
  branch.  The new bridge `det_ne_zero_of_diagDominantUpper` derives
  nonsingularity from the repository's `IsDiagDominantUpper` predicate, and the
  new solver/objective wrappers
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxSmallness_concreteDual`
  and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_concreteDual_solver_of_diagDominant`
  expose neither local determinant, auxiliary `κ`, auxiliary `K`, nor dual
  compact-budget hypotheses.  The remaining red dependencies on this route are
  proving or classifying local diagonal dominance and the canonical finite-max
  scalar smallness inequality for a concrete no-pivot stored QR loop.  Two
  weak-component passes for this exact surface are clean: focused build,
  executable lookup, `git diff --check`, touched-file marker scan, qualified
  axiom audit, PDF compile, text extraction, and rendered-page inspection all
  passed twice.  The repeated axiom audit reports only standard `propext`,
  `Classical.choice`, and `Quot.sound`, and the temporary axiom-audit file was
  deleted.

  Route-1 direct packaged-invariant handoff progress: the high-probability
  equation (8) RandNLA objective theorem can now consume the packaged
  off-diagonal-control invariant directly through
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver`.
  The source-shaped theorem is now a thin wrapper that derives
  `StoredQROffDiagonalControlInvariant` from
  `StoredQRSourceOffDiagonalControl` and calls the direct packaged theorem.
  This closes the solver-to-RandNLA handoff dependency for the selected
  route-1 invariant surface.  It does not close the red bottleneck itself: the
  remaining work is still to prove or classify the packaged
  off-diagonal-control invariant, local diagonal dominance, and the canonical
  finite-max scalar smallness inequality for a concrete no-pivot stored QR
  loop.  Two weak-component passes are clean: focused build, executable lookup,
  `git diff --check`, marker scan, qualified axiom audit, PDF compile, text
  extraction, and rendered-page inspection all passed twice.  The repeated
  axiom audit reports only standard `propext`, `Classical.choice`, and
  `Quot.sound`.

  Solver-facing row-budget finite-global-product wrappers: the local packaged
  row-budget route now has solver-layer global-product siblings,
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudgetControl_globalProduct`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_rowBudgetControl_globalProduct`.
  The first theorem composes the packaged row-budget source-control
  global-product certificate with the local `LSQRSolveBackwardError`
  handoff.  The second theorem derives the raw norm-square nonbreakdown field
  from local leading-block determinant, `κ∞`/self-norm, and dual compact-budget
  data before calling the first.  This closes another listed dependency on the
  row-budget route: the local solver surface no longer needs a family of
  per-pivot compact-product hypotheses.  The real red-bottleneck fields remain
  visible: the concrete loop still has to supply
  `StoredQRDisplayedRowBudgetControl`, local determinant/conditioning or dual
  budget data, scalar compact-product smallness, and final generic
  solver/preconditioner assembly.  Two weak-component validation passes are
  clean: repeated `git diff --check`, touched source Lean marker scan, focused
  LSQRSolve build, executable lookup, qualified axiom audit, PDF compile/text
  extraction, and rendered-page inspection passed.  The axiom audit reports
  only standard `propext`, `Classical.choice`, and `Quot.sound`.

  Route-1 finite-max packaged-invariant progress: the packaged invariant can
  now be derived from the two remaining visible fields on the diagonal-dominant
  branch.  The new constructor
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSmallness`
  consumes local `IsDiagDominantUpper` displayed leading blocks and the
  canonical scalar finite-max smallness inequality, then derives local
  determinant nonzeroness and per-pivot compact-product smallness internally.
  First weak-component validation is clean: focused build, executable lookup,
  `git diff --check`, marker scan, qualified axiom audit, PDF compile, text
  extraction, and rendered page inspection all passed.  The axiom audit reports
  only standard `propext`, `Classical.choice`, and `Quot.sound`.  This is a
  listed dependency closure; the red bottleneck is now sharply reduced to
  proving or classifying local diagonal dominance and the scalar finite-max
  smallness inequality for a concrete no-pivot stored QR loop.
  The repeated weak-component pass is also clean: focused build, executable
  lookup, `git diff --check`, marker scan, qualified axiom audit, PDF compile,
  text extraction, and rendered page inspection all passed again.  This
  checkpoint now has two consecutive clean passes.

  Cox--Higham row-budget route-elimination progress: the row-growth upper
  budget cannot be used as a hidden diagonal lower-bound proof.  The theorem
  `not_forall_leadingBlock_upper_det_activeBlockPos_offdiagBudget_implies_rowBudget_diag`
  uses the local `[[1,2],[0,1]]` witness with row budget `2`: upper-triangular
  nonsingular leading blocks and positive active-block mass hold, the strict
  upper entry satisfies the row budget, but the first displayed diagonal has
  magnitude `1`.  Thus the diagonal lower-bound/nonbreakdown field required by
  the row-budget source-control handoff is independent of row-growth upper
  estimates and active-block nonbreakdown.  Two weak-component passes are
  clean: focused LSQRSolve build, executable lookup, `git diff --check`,
  touched Lean marker scan, qualified axiom audit, PDF compile, text
  extraction, and rendered page inspection all passed twice.  This is route
  elimination, not closure of the positive theorem.  Remaining red-bottleneck
  progress must target a genuine diagonal lower-bound/nonbreakdown invariant,
  a stronger source theorem that supplies it, or an explicit domain assumption
  in the final solver-facing statement.

  Active max-pivot row-budget route-elimination progress: adding the active
  max-pivot policy still does not supply the missing diagonal lower-bound
  field.  The theorem
  `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_offdiagBudget_implies_rowBudget_diag`
  uses a two-stage witness: `[[2,1],[0,1]]` at the first stage, so the
  displayed active column is maximal, and `[[1,2],[0,1]]` at the second stage,
  so the row budget `2` still exceeds the first displayed diagonal magnitude
  `1`.  Thus the active max-pivot selector cannot be treated as a hidden proof
  of diagonal lower bounds.  First weak-component validation is clean:
  focused LSQRSolve build, executable lookup, `git diff --check`, marker scan,
  qualified axiom audit, PDF compile/text extraction, and rendered page 169
  all passed; the axiom audit reports only standard `propext`,
  `Classical.choice`, and `Quot.sound`.  The repeated weak-component pass is
  also clean with the same standard axiom audit result and readable rendered
  page 169.  This checkpoint now has two consecutive clean passes.  This
  remains route elimination; positive progress must close a genuine diagonal
  lower-bound/nonbreakdown dependency, rule out another listed route with
  evidence, or keep the field visible.

  Active-block-budget row-budget route-elimination progress: even adding
  active trailing-block magnitude control does not supply the missing diagonal
  lower-bound field.  The theorem
  `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_rowBudget_diag`
  reuses the two-stage active max-pivot witness and additionally assumes that
  the same nonnegative row budget bounds every active trailing-block entry at
  each displayed stage.  The witness satisfies that active-block budget with
  row budget `2`, but the second displayed stage still has diagonal magnitude
  `1` in the row where the strict upper entry has magnitude `2`.  Thus
  active-block magnitude control, active max-pivot selection, and row-growth
  upper bounds are still insufficient as a hidden diagonal lower-bound proof.
  Two weak-component validation passes are clean: repeated `git diff --check`,
  touched Lean marker scan, focused `LSQRSolve` build, executable lookup,
  qualified axiom audit, PDF compile/text extraction, and rendered-page
  inspection passed.  The axiom audit reports only standard `propext`,
  `Classical.choice`, and `Quot.sound`.  This remains route elimination; the
  positive route still needs a genuine diagonal lower-bound/nonbreakdown
  invariant, a source theorem supplying it, or an explicit visible assumption.

  Meta-property row-budget route-elimination progress: the theorem
  `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_property_implies_rowBudget_diag`
  shows that the same obstruction persists even after adding an arbitrary
  auxiliary side property `P A_hat rowBudget` to the attempted universal
  implication.  The proof chooses `P := True` and reuses the active-block-budget
  counterexample above.  This rules out the recurring weak route of appending
  unrelated scalar/product side conditions while leaving the diagonal
  lower-bound invariant itself unproved.  Two weak-component validation passes
  are clean: repeated `git diff --check`, touched Lean marker scan, focused
  `LSQRSolve` build, executable lookup, qualified axiom audit, PDF
  compile/text extraction, and rendered-page inspection passed.  The axiom
  audit reports only standard `propext`, `Classical.choice`, and `Quot.sound`.
  This remains route elimination, not positive diagonal nonbreakdown.

  Explicit-domain row-budget route choice: the final option above is now
  represented by a named Lean certificate rather than prose.  The structure
  `StoredQRDisplayedRowBudgetControl` packages the displayed strict-upper
  row-budget field together with the offdiag-row diagonal lower-bound field,
  and the source-control/solver wrappers
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudgetControl_product`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudgetControl_product`
  consume this package directly.  Two weak-component validations are clean:
  focused build, executable lookup, marker scan, qualified axiom audit, PDF
  compile, text extraction, and rendered-page inspection passed twice; the
  temporary audit file was deleted after validation.  This is a theorem-statement
  correction and explicit domain assumption, not a proof of the diagonal
  lower-bound/nonbreakdown invariant.  Remaining positive progress must either
  prove `StoredQRDisplayedRowBudgetControl` from a concrete pivoted/sorted loop
  or keep it visible in the scoped theorem while the full generic paper-level
  QR/preconditioner claim remains open.

  Scoped equation (8) row-budget-control handoff: the second option is now
  represented at the probability-theorem layer.  The RandNLA theorem
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_solver`
  consumes samplewise `StoredQRDisplayedRowBudgetControl`, derives the
  source-shaped stored-QR certificate, and reuses the high-probability rounded
  sampled-row objective theorem.  Focused build passed with only the
  pre-existing `HouseholderQR.lean` warnings.  First weak-component validation
  is clean: focused build, executable lookup, `git diff --check`, touched Lean
  marker scan, qualified axiom audit, PDF compile, text extraction, and
  rendered-page inspection all passed.  The repeated pass is also clean, and
  the temporary audit file was deleted after validation.  This is a scoped
  domain theorem, not a proof of the packaged row-budget certificate or a
  closure of the generic QR/preconditioner claim.

  Row-budget-control nonbreakdown reduction: the probability-theorem layer now
  also has the `κ∞`/dual-budget sibling
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_kappaInf_dualBudget_solver`.
  It closes one listed dependency reduction by deriving the raw norm-square
  nonbreakdown margin from the existing local QR inverse-budget adapter before
  calling the row-budget-control equation (8) theorem.  First weak-component
  validation is clean: focused build, executable lookup, marker scan, qualified
  axiom audit, PDF compile, text extraction, and rendered-page inspection
  passed; the repeated pass is also clean with the same standard axiom audit
  result.  This still leaves the real red-bottleneck fields visible:
  `StoredQRDisplayedRowBudgetControl` from a concrete pivoted/sorted loop,
  local determinant/`κ∞`/dual-budget data, and compact-product smallness.

  Signed-stage row-budget package constructor: the red bottleneck now has a
  direct theorem
  `StoredQRDisplayedRowBudgetControl.of_signed_stage_budgets_factor_of_normSqBudget`.
  It reuses the existing signed-stage Cox--Higham row-growth theorem and derives
  pivot-column zeroing from the norm-square nonbreakdown budget, producing the
  named certificate from signed-stage entry budgets plus the explicit
  offdiag-row diagonal lower-bound field.  First weak-component validation is
  clean: focused build, executable lookup, marker scan, qualified axiom audit,
  PDF compile, text extraction, and rendered-page inspection passed.  The
  repeated pass is also clean with the same standard axiom audit result and
  readable PDF pages 174--175.  This reduces the packaged-certificate dependency
  to the actual diagonal lower-bound/nonbreakdown invariant and concrete
  stage-budget recurrence.

  Uniform-stage row-budget package constructor: the red bottleneck now has the
  stop-time/monotonicity adapter
  `StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_factor_of_normSqBudget`.
  It specializes the packaged row-budget certificate to
  `rowBudget k i = stageBudget k` and uses `qrLeadingOffdiagStop_le` to remove
  the separate terminal row-budget-domination field.  First weak-component
  validation is clean: focused build, executable lookup, marker scan, qualified
  axiom audit, PDF compile, text extraction, and rendered-page inspection
  passed.  The repeated pass is also clean with the same standard axiom audit
  result and readable PDF pages 174--175.  The remaining package-producing
  fields are still the offdiag-row diagonal lower-bound/nonbreakdown invariant
  and the concrete monotone stage recurrence.

  Global compact-step and `κ∞`/dual-budget package constructors: the selected
  route now has
  `StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_of_normSqBudget`
  and
  `StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_kappaInf_dualBudget`.
  The norm-square constructor composes completed-column preservation,
  active-block recurrence, prefix-row recurrence, pivot maximality, the finite
  global compact-step recurrence, monotone stage budgets, and norm-square
  nonbreakdown into the named row-budget certificate.  The `κ∞`/dual-budget
  constructor removes the raw norm-square budget by reusing the existing
  leading-block inverse-budget adapter.  This is a direct dependency closure for
  the chosen route.  First weak-component validation is clean: whitespace,
  marker, focused-build, lookup, axiom, PDF compile/text, and rendered-page
  checks passed; the axiom audit reports only standard `propext`,
  `Classical.choice`, and `Quot.sound`.  The repeated weak-component pass is
  also clean with the same standard axiom audit result and readable rendered
  page 175.  The red bottleneck remains active on the offdiag-row diagonal
  lower-bound/nonbreakdown invariant, local determinant/conditioning fields,
  finite compact-product smallness, and the final QR/preconditioner theorem
  assembly.

  Canonical row-max row-budget bridge: the route now also has the safe-direction
  adapter
  `StoredQRDisplayedRowBudgetControl.of_sourceOffDiagonalControl_rowMaxBudget`,
  supported by the finite maximum definition `qrLeadingStrictUpperRowMaxBudget`
  and its entry/diagonal lemmas.  If the stronger source-shaped
  off-diagonal-control field is already available, this adapter packages it as
  `StoredQRDisplayedRowBudgetControl` by choosing each row budget to be the
  maximum strict-upper absolute value in that displayed row.  First
  weak-component validation is clean: whitespace, marker, focused-build,
  lookup, axiom, PDF compile/text, and rendered-page checks passed; the axiom
  audit reports only standard `propext`, `Classical.choice`, and `Quot.sound`.
  The repeated weak-component pass is also clean with the same standard axiom
  audit result, executable lookup exposure, PDF text extraction, and readable
  rendered page 175.
  This does not remove the diagonal lower-bound bottleneck; it prevents a
  future proof from re-proving or hiding the row-budget package when
  source-control data have already been supplied.

  Direct finite-max diagonal-dominant RandNLA wrapper: the probability layer now
  also has
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver_of_diagDominant_finiteMaxSmallness`.
  It builds `StoredQROffDiagonalControlInvariant` samplewise from local
  `IsDiagDominantUpper` leading blocks and the canonical scalar finite-max
  smallness inequality by reusing
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSmallness`,
  then calls the direct packaged off-diagonal-control RandNLA theorem.  This
  closes the package-to-probability handoff on the diagonal-dominant finite-max
  route.  It does not close the red bottleneck itself: local diagonal dominance
  and the canonical scalar finite-max smallness inequality remain visible
  source/domain assumptions until they are proved for a concrete no-pivot stored
  QR loop or deliberately retained as scoped assumptions.  First
  weak-component validation is clean: focused build, executable lookup, `git
  diff --check`, marker scan, qualified axiom audit, PDF compile/text, and
  rendered-page inspection passed; the axiom audit reports only standard
  `propext`, `Classical.choice`, and `Quot.sound`.
  The repeated weak-component pass is also clean with the same standard axiom
  audit result and readable rendered pages 115 and 186.  This checkpoint now
  has two consecutive clean passes; the remaining red dependencies are local
  diagonal dominance and the canonical scalar finite-max smallness inequality
  for a concrete no-pivot stored QR loop, or an explicit decision to retain
  those as scoped source/domain assumptions.

  Stronger exact-no-pivot route elimination: the finite-max route cannot be
  rescued by pairing diagonal dominance with another final-block property
  derived from the standard exact recurrence.  The theorem
  `not_forall_exact_trailing_householder_sequence_implies_diagDominant_and_property`
  says that, for any final-block property `P`, the exact two-step no-pivot
  Householder witness refutes a universal implication to
  `IsDiagDominantUpper` and `P`.  This directly rules out treating the scalar
  finite-max smallness side condition as a hidden source of diagonal dominance.
  First weak-component validation is clean: `git diff --check`, marker scan,
  focused LSQRSolve build, executable lookup exposure, qualified axiom audit,
  PDF compile/text extraction, and rendered page 168 passed.  Repeated
  validation is also clean with the same standard axiom audit result and
  readable rendered page 168.  This closes the route-elimination dependency:
  route 1 cannot be completed by extracting diagonal dominance plus scalar
  finite-max smallness from the ordinary exact no-pivot recurrence.

  Active max-pivot row-budget package dependency: the packaged global
  compact-step row-budget constructors now have active-pivot-policy variants,
  `StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_activeMaxPivot_of_normSqBudget`
  and
  `StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_activeMaxPivot_kappaInf_dualBudget`.
  These derive the raw pivot-maximality field internally from
  `householderActiveMaxPivotColumn_pivot_max`, so the route can expose the
  algorithmic policy equation that the displayed pivot column is the finite
  active max-pivot selector.  This reduces the red bottleneck by one listed
  field, but it does not change the remaining hard dependencies: a concrete
  loop still needs diagonal lower bounds/off-diagonal control, local
  determinant or conditioning data, nonbreakdown, compact-product smallness,
  and final solver/preconditioner assembly.  Focused LSQRSolve build passed.
  First weak-component validation is clean: whitespace, marker scan, focused
  build, executable lookup, qualified axiom audit, PDF compile/text extraction,
  and rendered pages 175--176 passed.  The repeated pass is also clean with
  the same standard axiom audit result and readable rendered pages 175--176.
  This dependency now has two consecutive clean passes.

  Probability-level active max-pivot wrapper: the RandNLA equation (8)
  active/prefix global-product `κ∞` theorem now has an active-pivot-policy
  sibling,
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver`.
  It derives the raw pivot-maximality field from
  `householderActiveMaxPivotColumn_pivot_max` using the samplewise policy
  equation that the displayed pivot column is the finite active max-pivot
  selector, then applies the existing active/prefix global-product theorem.
  The horizon-clamped sibling
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver_of_horizonBudget`
  uses the same pivot-maximality derivation but calls the LS.2g-hz
  horizon-clamped `κ∞`/dual-budget theorem, removing the samplewise global
  budget-monotonicity field from this active-pivot probability surface.  The
  full validation gate is clean, with the same standard axiom audit result and
  readable rendered theorem/open-bottleneck pages.
  This directly closes another listed dependency on the selected route; it does
  not change the remaining hard dependencies: diagonal lower bounds/off-diagonal
  control, local determinant or conditioning data, nonbreakdown,
  compact-product smallness, and final solver/preconditioner assembly.  First
  weak-component validation is clean: whitespace, marker scan, focused RandNLA
  least-squares build, executable lookup, qualified axiom audit, PDF
  compile/text extraction, and rendered page 185 passed.  A repeated pass is
  also clean with the same standard axiom audit result and readable rendered
  page 185.  This dependency now has two consecutive clean passes.

  Probability-level active max-pivot row-budget wrapper: the finite
  global-product row-budget equation (8) theorem now has a sibling,
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver`,
  that builds `StoredQRDisplayedRowBudgetControl` internally from the
  active-max-pivot global compact-step constructor.  This closes the assembly
  edge from the packaged active-pivot row-budget certificate to the RandNLA
  objective theorem.  It does not change the remaining hard dependencies:
  diagonal lower bounds/off-diagonal control, local determinant or conditioning
  data, nonbreakdown, compact-product smallness, and final generic
  solver/preconditioner assembly.  First weak-component validation is clean:
  whitespace, marker scan, focused RandNLA least-squares build, executable
  lookup, qualified axiom audit, PDF compile/text extraction, and rendered page
  185 passed.  The axiom audit reports only standard `propext`,
  `Classical.choice`, and `Quot.sound`.  The repeated validation pass is also
  clean with the same standard axiom audit result and readable rendered page
  185.  This checkpoint now has two consecutive clean passes.

  Solver-facing active max-pivot wrapper: the local active/prefix
  global-product `κ∞` QR certificate now has an active-pivot-policy sibling,
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_offdiag_rows`.
  It derives the raw pivot-maximality field from
  `householderActiveMaxPivotColumn_pivot_max` using the policy equation that
  the displayed pivot column is the finite active max-pivot selector, then
  applies the existing raw-pivot solver theorem.  This closes the pivot-policy
  field at the local solver layer, complementing the existing probability-level
  active-pivot wrappers.  It does not change the remaining hard dependencies:
  diagonal lower bounds/off-diagonal control, local determinant or conditioning
  data, nonbreakdown, compact-product smallness, and final generic
  solver/preconditioner assembly.  Two weak-component validation passes are
  clean: repeated `git diff --check`, touched source Lean marker scan, focused
  LSQRSolve build, executable lookup, qualified axiom audit, PDF compile/text
  extraction, and rendered-page inspection of pages 184--185 passed.  The
  axiom audit reports only standard `propext`, `Classical.choice`, and
  `Quot.sound`.

  Scalar row-max defect route elimination: the route-1 scalar-defect condition
  cannot be obtained from the ordinary exact no-pivot recurrence alone.
  `LSQRSolve.lean` now proves
  `exactHouseholderQRDiagDominanceCounterexample_rowMaxDiagDefectBudget_pos`,
  showing that the exact two-stage no-pivot Householder counterexample has
  positive `storedQRRowMaxDiagDefectBudget`, and
  `not_forall_exact_trailing_householder_sequence_implies_rowMaxDiagDefectBudget_nonpos`,
  ruling out a universal theorem from only the exact trailing recurrence, valid
  signed squared-norm identities, and nonzero Householder denominators to the
  nonpositive scalar defect condition.  This is a route-elimination dependency
  closure for the red bottleneck: a positive proof still needs a stronger
  computed-loop/off-diagonal-control invariant, a pivoted/sorted theorem
  family, or an explicit visible assumption, plus determinant/conditioning,
  norm-square, and scalar product-smallness fields.  First weak-component
  validation is clean: `git diff --check`, touched source marker scan, focused
  LSQRSolve build, executable lookup, qualified axiom audit, PDF
  compile/text extraction, and rendered-page inspection of pages 177--179
  passed.  The axiom audit reports only standard `propext`,
  `Classical.choice`, and `Quot.sound`.  Repeated validation is also clean
  with the same standard axiom audit result, executable lookup exposure, PDF
  text extraction, and readable rendered pages 177--179.  This
  route-elimination dependency now has two consecutive clean passes.

  Probability-level scalar row-max-defect wrapper: the RandNLA least-squares
  probability layer now has
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowMaxDiagDefect_globalProduct_solver`.
  It builds the samplewise `StoredQRDisplayedRowBudgetControl` certificate from
  the scalar condition `storedQRRowMaxDiagDefectBudget <= 0`, derives the
  per-pivot compact-product family from the finite scalar condition
  `storedQRCompactSequenceProductBudget < 1`, and applies the existing
  row-budget-control high-probability equation (8) objective theorem.  This is
  a listed assembly dependency only: the scalar defect condition, determinant
  or conditioning fields, norm-square nonbreakdown, scalar product smallness,
  and final generic QR/preconditioner theorem remain open or visible.  First
  weak-component validation is clean: `git diff --check`, touched source marker
  scan, focused LeastSquaresSketch build, executable lookup, qualified axiom
  audit, PDF compile/text extraction, and rendered-page inspection of pages
  114--118 passed.  The axiom audit reports only standard `propext`,
  `Classical.choice`, and `Quot.sound`.  Repeated validation is also clean
  with the same standard axiom audit result, executable lookup exposure, PDF
  text extraction, and readable rendered pages 114--118.  This assembly
  dependency now has two consecutive clean passes.

  Probability-level primitive norm-square/off-diagonal-product wrapper: the
  RandNLA least-squares probability layer now has
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_leadingBlock_det_ne_zero_normSqBudget_offdiag_product_solver`.
  It constructs `StoredQRSourceOffDiagonalControl` samplewise from
  leading-block determinant nonzeroness, the dimensioned norm-square
  nonbreakdown margin, row-wise off-diagonal domination, and per-pivot
  compact-product smallness, then applies the existing source-shaped
  high-probability equation (8) objective theorem.  This is a listed assembly
  dependency only: determinant/nonbreakdown, off-diagonal domination,
  compact-product smallness, and the final generic QR/preconditioner theorem
  remain open or visible.  First weak-component validation is clean: `git diff
  --check`, touched source marker scan, focused LeastSquaresSketch build,
  executable lookup, qualified axiom audit, PDF compile/text extraction, and
  rendered-page inspection of pages 114--119 passed.  The axiom audit reports
  only standard `propext`, `Classical.choice`, and `Quot.sound`.  Repeated
  validation is also clean with the same standard axiom audit result,
  executable lookup exposure, PDF text extraction, and readable rendered pages
  114--119.  This dependency now has two consecutive clean passes.

  Diagonal dominance to scalar row-max-defect bridge: the local row-max and
  diagonal-dominant route surfaces are now connected by
  `storedQRRowMaxDiagDefectBudget_nonpos_of_diagDominant` and
  `StoredQRDisplayedRowBudgetControl.of_diagDominant`.  If every displayed
  leading block is `IsDiagDominantUpper`, then the row-wise strict-upper
  maximum is below the displayed diagonal, so the finite scalar defect is
  nonpositive and the packaged row-budget certificate follows.  This closes a
  listed duplicate-assumption bridge only: it reuses local diagonal dominance
  when supplied, and it does not prove diagonal dominance for generic no-pivot
  QR.  First weak-component validation is clean: `git diff --check`, touched
  source marker scan, focused LSQRSolve build, executable lookup, qualified
  axiom audit, PDF compile/text extraction, and rendered-page inspection of
  pages 177--179 passed.  The axiom audit reports only standard `propext`,
  `Classical.choice`, and `Quot.sound`.  Repeated validation is also clean
  with the same standard axiom audit result, executable lookup exposure, PDF
  text extraction, and readable rendered pages 177--179.  This dependency now
  has two consecutive clean passes.

  Exact/zero-compact product-smallness endpoint: `LSQRSolve.lean` now proves
  `storedQRCompactSequenceProductBudget_lt_one_of_relativeBudget_eq_zero`.
  When the stored compact sequence relative budget is exactly zero, every
  per-pivot compact-product expression is zero, so the global finite
  compact-product budget is strictly below one.  This closes a listed
  dependency only for the exact/zero-compact branch of the active/prefix QR
  route.  It does not prove the positive floating-point compact-product
  smallness inequality for `storedQRCompactSequenceRelativeBudget > 0`, and it
  does not close the remaining route-1 dependencies: local diagonal dominance
  or off-diagonal control from the concrete loop, determinant/conditioning
  fields, norm-square nonbreakdown, and the final generic equation (8)
  QR/preconditioner theorem.  Two weak-component passes are clean: focused
  LSQRSolve build, executable lookup, whitespace check, touched-source marker
  scan, qualified axiom audit, PDF compile/text extraction, and rendered-page
  inspection of the compact-product section passed with only standard
  `propext`, `Classical.choice`, and `Quot.sound` in the axiom audit.

  Positive-budget relative-cap reduction: `LSQRSolve.lean` now proves
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_relativeBudget_le`.
  Under local diagonal dominance, if the stored compact sequence relative budget
  is bounded by a nonnegative explicit cap `cmax`, then the global
  compact-product budget is below one whenever the canonical finite-max scalar
  product inequality holds with `cmax`.  This directly reduces the
  positive-budget compact-product blocker to two listed dependencies: prove the
  relative-budget cap and prove the scalar inequality using that cap.  It does
  not prove those dependencies, and it does not affect the remaining local
  diagonal dominance/off-diagonal control, determinant/conditioning,
  norm-square nonbreakdown, or final generic equation (8) QR/preconditioner
  theorem.

  Uniform per-step compact-panel cap reduction: `HouseholderQR.lean` now proves
  `storedQRCompactSequenceRelativeBudget_le_mul_of_step_le`, and
  `LSQRSolve.lean` now proves
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_stepBudget_le`.
  The positive-budget compact-product route is reduced one level further:
  instead of an arbitrary sequence cap, it is enough to prove a uniform
  one-step compact-panel relative cap `cStep` and the scalar inequality with
  `n * cStep`.  This closes only the finite-sum reduction; the one-step cap,
  scalar smallness, local diagonal dominance/off-diagonal control,
  determinant/conditioning/nonbreakdown, and final generic equation (8)
  QR/preconditioner theorem remain open or visible.  Two weak-component
  passes are clean: focused LSQRSolve build, executable lookup, whitespace
  check, touched-source marker scan, qualified axiom audit, PDF
  compile/text extraction, and rendered-page inspection of pages 187--188
  passed.  The axiom audit reports only standard `propext`,
  `Classical.choice`, and `Quot.sound`.

  Vector-level compact column/RHS cap reduction: `HouseholderApply.lean` now
  proves `householderCompactPanelRelativeBudget_le_mul_add_of_column_rhs_le`,
  `HouseholderQR.lean` now proves
  `storedQRCompactStepRelativeBudget_le_mul_add_of_column_rhs_le`, and
  `LSQRSolve.lean` now proves
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsBudget_le`.
  This closes the next listed reduction in the positive-budget compact-product
  route: vector-level column/RHS caps `cCol,cRhs` imply a one-step cap
  `n * cCol + cRhs`, a sequence cap `n * (n * cCol + cRhs)`, and the finite-max
  product threshold under the corresponding scalar smallness inequality.  It
  still does not prove the vector-level caps, local diagonal dominance or
  off-diagonal control, determinant/conditioning/nonbreakdown, scalar
  product-smallness from a concrete loop, or the final generic equation (8)
  QR/preconditioner theorem.  Two weak-component passes are clean: whitespace
  checks, touched-source marker scans, focused LSQRSolve builds, executable
  lookup, qualified axiom audits, PDF compile/text extraction, and rendered-page
  inspection of pages 187--189 all passed.  The axiom audit reports only
  standard `propext`, `Classical.choice`, and `Quot.sound`.

  Primitive norm-budget compact column/RHS cap reduction: `HouseholderApply.lean`
  now proves `householderCompactRelativeBudget_le_of_normBudget_le_mul` and
  `householderCompactPanelRelativeBudget_le_mul_add_of_normBudget_le_mul`;
  `HouseholderQR.lean` proves
  `storedQRCompactStepRelativeBudget_le_mul_add_of_normBudget_le_mul`; and
  `LSQRSolve.lean` proves
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsNormBudget_le`.
  This is the next listed dependency closure in the positive-budget
  compact-product route: primitive norm-budget inequalities
  `householderCompactNormBudget <= c * vecNorm2` imply the already-normalized
  vector relative caps, then the same one-step cap `n * cCol + cRhs`, sequence
  cap `n * (n * cCol + cRhs)`, and finite-max scalar threshold.  It still does
  not prove the primitive norm-budget inequalities from the FP model, the
  scalar smallness inequality, local diagonal dominance/off-diagonal control,
  determinant/conditioning/nonbreakdown, or the final generic equation (8)
  QR/preconditioner theorem.  Two weak-component validations are clean:
  whitespace checks, touched-source marker scans, focused HouseholderApply,
  HouseholderQR, and LSQRSolve builds, executable lookup, qualified axiom
  audits, PDF compile/text extraction, and rendered-page inspection of pages
  187--190 passed twice.  The axiom audit reports only standard `propext`,
  `Classical.choice`, and `Quot.sound`.

  Componentwise compact column/RHS cap reduction: `HouseholderApply.lean` now
  proves `householderCompactNormBudget_le_mul_of_componentBudget_le_mul_abs`,
  `householderCompactRelativeBudget_le_of_componentBudget_le_mul_abs`, and
  `householderCompactPanelRelativeBudget_le_mul_add_of_componentBudget_le_mul_abs`;
  `HouseholderQR.lean` proves
  `storedQRCompactStepRelativeBudget_le_mul_add_of_componentBudget_le_mul_abs`;
  and `LSQRSolve.lean` proves
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsComponentBudget_le`.
  This is the next listed dependency closure below primitive norm budgets:
  entrywise component inequalities
  `householderCompactComponentBudget_i <= c * |input_i|` imply the norm-budget
  caps, then the same one-step cap `n * cCol + cRhs`, sequence cap
  `n * (n * cCol + cRhs)`, and finite-max scalar threshold.  It still does not
  prove the entrywise inequalities from the FP model, the scalar smallness
  inequality, local diagonal dominance/off-diagonal control,
  determinant/conditioning/nonbreakdown, or the final generic equation (8)
  QR/preconditioner theorem.  Two weak-component validations are clean:
  whitespace checks, touched-source marker scans, focused LSQRSolve builds,
  executable lookup, qualified axiom audits, PDF compile/text extraction, and
  rendered-page inspection of pages 188--190 passed twice.  The axiom audit
  reports only standard `propext`, `Classical.choice`, and `Quot.sound`.

  Explicit norm-coefficient compact-product reduction:
  `HouseholderApply.lean` now proves the valid primitive route below the
  norm-budget adapter.  `householderAbsDotBudget_le_vecNorm2_mul` bounds the
  absolute dot budget by Cauchy--Schwarz; `householderCompactUpdateCoeff` and
  `householderCompactNormBudgetCoeff` are explicit reflector-dependent
  coefficients; `householderCompactComponentBudget_le_updateCoeff_mul_norm`
  charges the nonlocal update to `||input||_2 * |v_i|` and the final
  subtraction to `|input_i|`; and
  `householderCompactNormBudget_le_normBudgetCoeff_mul` gives the norm-budget
  cap.  `HouseholderQR.lean` packages this as
  `storedQRCompactStepNormBudgetCoeff` and
  `storedQRCompactStepRelativeBudget_le_mul_add_normBudgetCoeff`;
  `LSQRSolve.lean` proves
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeff_le`.
  This closes a listed dependency reduction and corrects the over-strong
  entrywise-relative direction.  Remaining positive progress must prove a
  uniform coefficient bound for a concrete stored loop, scalar smallness, local
  diagonal dominance/off-diagonal control, or the determinant/conditioning
  fields.  Two weak-component validation passes are clean: focused builds,
  repeated `git diff --check`, touched-file marker scan, executable lookup,
  qualified axiom audit, PDF compile, targeted `pdftotext`, and rendered pages
  188--192 all passed.

  Canonical norm-coefficient maximum reduction:
  `HouseholderQR.lean` now proves
  `storedQRCompactStepNormBudgetCoeff_nonneg`.  `LSQRSolve.lean` defines
  `storedQRCompactStepNormBudgetCoeffBudget`, proves
  `storedQRCompactStepNormBudgetCoeff_le_budget` and
  `storedQRCompactStepNormBudgetCoeffBudget_nonneg`, and specializes the
  compact-product theorem as
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeffBudget`.
  This closes the listed dependency "choose the uniform reflector coefficient
  by finite maximum" and replaces the arbitrary `cHH` field by a canonical
  displayed max.  Remaining positive progress must prove scalar smallness for
  that max, local diagonal dominance/off-diagonal control, or the
  determinant/conditioning fields.  Two weak-component validation passes are
  clean: repeated `git diff --check`, touched-file marker scans, focused
  LSQRSolve build, executable lookup, qualified axiom audits, PDF compile/text
  extraction, and rendered pages 188--193 all passed.

  Coefficient-maximum handoff progress: the canonical coefficient maximum now
  reaches the packaged route-1 invariant and the RandNLA equation (8) objective
  wrapper.  `LSQRSolve.lean` proves
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxNormBudgetCoeffSmallness`,
  and `LeastSquaresSketch.lean` proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver_of_diagDominant_finiteMaxNormBudgetCoeffSmallness`.
  This closes the listed dependency "thread the canonical coefficient maximum
  through the equation (8) handoff".  Remaining positive progress must prove
  scalar smallness for that maximum, local diagonal dominance/off-diagonal
  control, or determinant/conditioning fields.  Two weak-component passes are
  clean: repeated `git diff --check`, touched-file marker scans, focused RandNLA
  build, executable lookup, qualified axiom audits, PDF compile/text extraction,
  and rendered pages 190--192 all passed.

  Bounded scalar-smallness progress: `LSQRSolve.lean` now proves
  `storedQRCompactNormBudgetCoeffSmallness_of_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeffBudget_bounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxNormBudgetCoeffBoundedSmallness`.
  This reduces the coefficient-max scalar-smallness dependency to displayed
  route constants \(D_{\max},C_{\max},N_{\max}\) that dominate the canonical
  diagonal-dominant inverse budget, coefficient maximum, and pivot-column norm
  budget.  Remaining positive progress must prove those upper bounds, the
  cleaner scalar inequality, local diagonal dominance/off-diagonal control, or
  determinant/conditioning fields.  Two weak-component validation passes are
  clean: repeated `git diff --check`, touched Lean marker scans, focused
  LSQRSolve builds, executable lookup, qualified axiom audits, PDF compile/text
  extraction, and rendered pages 190--193 all passed.

  Pointwise route-bound progress: `LSQRSolve.lean` now proves
  `storedQRDiagDominantInvFactorBudget_le_of_forall_le`,
  `storedQRPivotColumnNormBudget_le_of_forall_le`,
  `storedQRCompactStepNormBudgetCoeffBudget_le_of_forall_le`,
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeffBudget_pointwise_bounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxNormBudgetCoeffPointwiseBounds`.
  This reduces the displayed-upper-bound dependency to per-pivot estimates plus
  nonnegativity of the displayed constants for the zero-pivot edge case.
  Remaining positive progress must prove those pointwise estimates, the cleaner
  scalar inequality, local diagonal dominance/off-diagonal control, or
  determinant/conditioning fields.  Two weak-component validation passes are
  clean: repeated focused LSQRSolve builds, executable lookup, touched Lean
  marker scans, qualified axiom audits, PDF compile/text extraction, and
  rendered pages 190--194 passed.

  Solver-facing pointwise handoff progress: `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_diagDominant_finiteMaxNormBudgetCoeffPointwiseBounds_concreteDual`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxNormBudgetCoeffPointwiseBounds_concreteDual`.
  These wrappers compose the pointwise product-budget route into the
  concrete-dual QR solve certificate, with the second wrapper deriving
  leading-block determinant nonzeroness from local diagonal dominance.  This is
  a solver-surface composition closure only.  Remaining positive progress must
  still prove the pointwise estimates, the cleaner scalar inequality, local
  diagonal dominance/off-diagonal control for a concrete loop, or
  determinant/conditioning fields.  Two weak-component validation passes are
  clean: repeated `git diff --check`, touched Lean marker scans, focused
  LSQRSolve builds, executable lookup, qualified axiom audits, PDF compile/text
  extraction, and rendered pages 191--195 passed.

  Per-pivot beta-norm coefficient reduction progress: `HouseholderApply.lean`
  now proves the exact identity
  `householderCompactNormBudgetCoeff_eq_u_add_abs_beta_norm_sq_mul_factor`,
  exposes the nonnegative factor
  `householderCompactNormBudgetCoeffFactor`, and proves
  `householderCompactNormBudgetCoeff_le_of_abs_beta_norm_sq_le`.
  `HouseholderQR.lean` lifts this to stored signed stages via
  `storedQRCompactStepNormBudgetCoeff_le_of_abs_beta_norm_sq_le` and
  `storedQRCompactStepNormBudgetCoeff_le_of_forall_abs_beta_norm_sq_le`.
  `LSQRSolve.lean` then proves
  `storedQRCompactStepNormBudgetCoeffBudget_le_of_forall_abs_beta_norm_sq_le`,
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_absBetaNormSq_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_absBetaNormSqPointwiseBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxAbsBetaNormSqPointwiseBounds`.
  This closes a listed dependency reduction: the previous abstract coefficient
  pointwise estimate can be supplied by a signed-stage estimate
  `|beta_k| * ||v_k||_2^2 <= Bmax` and the explicit scalar
  `u + Bmax * householderCompactNormBudgetCoeffFactor fp m`.  It does not close
  the `Bmax` estimate itself, local diagonal dominance/off-diagonal control,
  determinant/conditioning fields, the scalar smallness inequality, or the final
  generic QR/preconditioner theorem.
  Two weak-component validation passes are clean: repeated focused LSQRSolve
  builds, executable lookup, touched-source marker scans, qualified axiom
  audits, PDF compile/text extraction, and rendered page inspections passed,
  with only the pre-existing HouseholderQR unused-variable warnings.

  Exact Householder-normalization coefficient progress: `HouseholderSpec.lean`
  now proves `abs_householderBeta_mul_vecNorm2_sq_eq_two` and
  `abs_householderBeta_mul_vecNorm2_sq_le_two`, turning the local
  `householderBeta_mul_inner_self_eq_two` denominator identity into the exact
  coefficient-route bound `|beta| * ||v||_2^2 = 2`.  `HouseholderQR.lean`
  packages this for stored signed stages and the source-shaped nonbreakdown
  denominator hypothesis via
  `storedQRSignedStage_abs_beta_norm_sq_eq_two_of_den_ne_zero`,
  `storedQRCompactStepNormBudgetCoeff_le_of_forall_source_den_ne_zero`, and
  related one-stage/uniform wrappers.  `LSQRSolve.lean` proves
  `storedQRCompactStepNormBudgetCoeffBudget_le_of_forall_source_den_ne_zero`,
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenPointwiseBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenPointwiseBounds`.
  This closes the listed `Bmax` estimate dependency with the concrete value
  `Bmax = 2` under explicit source nonbreakdown.  Remaining positive progress
  must prove scalar smallness, local diagonal dominance/off-diagonal control,
  inverse-factor and pivot-column pointwise bounds, determinant/conditioning
  fields, or a theorem-statement correction.  Focused LSQRSolve build passed,
  and two weak-component passes are clean: repeated `git diff --check`, touched
  Lean marker scans, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LeastSquares.LSQRSolve`, executable
  lookup, qualified axiom audit for the eleven new theorem names, theorem PDF
  compile, targeted `pdftotext`, and rendered pages 190--193 passed.  The axiom
  audit reported only standard `propext`, `Classical.choice`, and
  `Quot.sound`, and the temporary axiom-audit file was deleted.

  Source-facing scalar-smallness normalization progress:
  `LSQRSolve.lean` now proves
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_simple_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenSimpleBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenSimpleBounds`.
  These theorems rewrite the expanded `Cmax = u + 2F_m` source-denominator
  smallness condition into the compact route certificate
  `2 * Dmax * (m * ((n * (n + 1) * Cmax * Nmax)^2)) < 1`.  This is a listed
  theorem-statement normalization only; remaining positive progress must prove
  the numerical scalar inequality, local diagonal dominance/off-diagonal
  control, inverse-factor and pivot-column pointwise bounds,
  determinant/conditioning fields, or a theorem-statement correction.  Focused
  LSQRSolve build passed, and two weak-component passes are clean: repeated
  `git diff --check`, touched Lean marker scans, focused LSQRSolve builds,
  executable lookup, qualified axiom audit for the three new theorem names,
  theorem PDF compile, targeted `pdftotext`, and rendered pages 192--193
  passed.  The axiom audit reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`, and the temporary axiom-audit file was
  deleted.

  Source-denominator scalar cap bridge progress:
  `LSQRSolve.lean` now proves
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_cap_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenCapBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenCapBounds`.
  These theorems are a listed scalar-smallness dependency reduction: they show
  that the source-facing condition with
  `u + 2 * householderCompactNormBudgetCoeffFactor fp m` follows from upper
  caps `fp.u <= Ucap`,
  `householderCompactNormBudgetCoeffFactor fp m <= Fcap`, and the displayed
  scalar inequality with `Ucap + 2 * Fcap`.  Remaining positive progress must
  prove the cap estimates, the numerical scalar inequality, local diagonal
  dominance/off-diagonal control, inverse-factor and pivot-column pointwise
  bounds, determinant/conditioning fields, or a theorem-statement correction.
  Focused LSQRSolve build passed, and two weak-component passes are clean:
  repeated `git diff --check`, production Lean marker scans, focused LSQRSolve
  builds, executable lookup, qualified axiom audits, theorem PDF compile,
  targeted `pdftotext`, and rendered pages 192--195 passed.  The axiom audit
  reported only standard `propext`, `Classical.choice`, and `Quot.sound`, and
  the temporary audit file was deleted.

  Householder coefficient-factor cap progress:
  `HouseholderApply.lean` now proves
  `householderCompactNormBudgetCoeffFactor_le_of_u_gamma_le`.
  This theorem is a listed cap-estimate dependency for the preceding
  source-denominator cap bridge: it bounds
  `householderCompactNormBudgetCoeffFactor fp m` by the explicit expression in
  displayed caps `Ucap` and `Gcap` whenever `fp.u <= Ucap`,
  `gamma fp m <= Gcap`, and the caps are nonnegative.  Remaining positive
  progress must prove the primitive `u`/`gamma` caps, the scalar cap
  inequality, local diagonal dominance/off-diagonal control, inverse-factor and
  pivot-column pointwise bounds, determinant/conditioning fields, source
  nonbreakdown, or a theorem-statement correction.  Two weak-component passes
  are clean: repeated `git diff --check`, production Lean marker scans,
  focused HouseholderApply and LSQRSolve builds, executable lookup, qualified
  axiom audit, theorem PDF compile, targeted `pdftotext`, and rendered pages
  192--193 passed.  The axiom audit reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`.

  Gamma cap progress:
  `Rounding.lean` now proves `gamma_le_of_u_le_cap` and
  `gamma_le_Gcap_of_u_le_cap`.  These are listed primitive cap-estimate
  dependencies for the Householder coefficient-factor cap: from
  `fp.u <= Ucap`, `(m : ℝ) * Ucap < 1`, and the displayed rational domination
  `((m : ℝ) * Ucap)/(1 - (m : ℝ) * Ucap) <= Gcap`, the route obtains
  `gamma fp m <= Gcap`.  Remaining positive progress must prove the primitive
  unit-roundoff cap, the scalar cap inequality, local diagonal
  dominance/off-diagonal control, inverse-factor and pivot-column pointwise
  bounds, determinant/conditioning fields, source nonbreakdown, or a
  theorem-statement correction.  Two weak-component passes are clean: repeated
  `git diff --check`, production Lean marker scans, focused
  Rounding/HouseholderApply/LSQRSolve builds, executable lookup, qualified
  axiom audit, theorem PDF compile, targeted `pdftotext`, and rendered pages
  193--194 passed.  The axiom audit reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`.

  Composed factor-cap progress:
  `HouseholderApply.lean` now proves
  `householderCompactNormBudgetCoeffFactor_le_of_u_cap_gamma_cap`, which
  composes the Householder coefficient-factor cap with the rounding gamma cap.
  The route now obtains the displayed polynomial factor bound from
  `fp.u <= Ucap`, `(m : ℝ) * Ucap < 1`, and
  `((m : ℝ) * Ucap)/(1 - (m : ℝ) * Ucap) <= Gcap`, without a separate
  `gamma fp m <= Gcap` field.  Remaining positive progress must prove the
  primitive unit-roundoff cap, the scalar cap inequality, local diagonal
  dominance/off-diagonal control, inverse-factor and pivot-column pointwise
  bounds, determinant/conditioning fields, source nonbreakdown, or a
  theorem-statement correction.  Two weak-component passes are clean: repeated
  `git diff --check`, production Lean marker scans, focused
  HouseholderApply/LSQRSolve builds, executable lookup, qualified axiom audit,
  theorem PDF compile, targeted `pdftotext`, and rendered pages 193--194
  passed.  The axiom audit reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`.

  Source-denominator cap-route progress:
  `LSQRSolve.lean` now proves
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_uGammaCapBounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenUGammaCapBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenUGammaCapBounds`.
  These compose the unit-roundoff-derived Householder coefficient-factor cap
  into the scalar-smallness, compact-product, and off-diagonal-control invariant
  surfaces.  Two weak-component passes are clean: repeated `git diff --check`,
  production Lean marker scans, focused LSQRSolve builds, executable lookup,
  qualified axiom audits, theorem PDF compile, targeted `pdftotext`, and
  rendered pages 193--195 passed.  The axiom audit reported only standard
  `propext`, `Classical.choice`, and `Quot.sound`; the temporary audit file was
  deleted.  Remaining positive progress must prove the primitive unit-roundoff
  cap or rational `Gcap` domination, the scalar cap inequality, local diagonal
  dominance/off-diagonal control, inverse-factor and pivot-column pointwise
  bounds, determinant/conditioning fields, source nonbreakdown, or a
  theorem-statement correction.  Focused LSQRSolve build passed; full two-pass
  validation is in progress.

  Unit-roundoff-cap route elimination:
  `Model.lean` now defines `FPModel.exactWithUnitRoundoff` and proves
  `FPModel.not_forall_u_le_cap`.  Since exact arithmetic can be packaged as an
  `FPModel` with any nonnegative declared unit roundoff, no theorem can derive
  a fixed numerical cap `fp.u <= Ucap` from the abstract model alone.  Two
  weak-component passes are clean: repeated `git diff --check`, production Lean
  marker scans, focused Model builds, executable lookup, qualified axiom audits,
  theorem PDF compile, targeted `pdftotext`, and rendered page 194 passed.  The
  axiom audit reported only standard `propext`, `Classical.choice`, and
  `Quot.sound`.  Remaining positive progress must prove rational `Gcap`
  domination, the scalar cap inequality, local diagonal dominance/off-diagonal
  control, inverse-factor and pivot-column pointwise bounds,
  determinant/conditioning fields, source nonbreakdown, or introduce a concrete
  machine model with a formal unit-roundoff cap.

  Rational gamma cap specialization:
  `LSQRSolve.lean` now proves
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_uRationalGammaCapBounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenURationalGammaCapBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenURationalGammaCapBounds`.
  These specialize the preceding source-denominator route to
  `Gcap = (m * Ucap)/(1 - m * Ucap)`, so the rational-domination field closes
  by reflexivity.  Two weak-component passes are clean: repeated
  `git diff --check`, production Lean marker scans, focused LSQRSolve builds,
  executable lookup, qualified axiom audits, theorem PDF compile, targeted
  `pdftotext`, and rendered pages 194--195 passed.  The axiom audit reported
  only standard `propext`, `Classical.choice`, and `Quot.sound`.  Remaining
  positive progress must prove the primitive
  unit-roundoff cap, the displayed scalar cap inequality, local diagonal
  dominance/off-diagonal control, inverse-factor and pivot-column pointwise
  bounds, determinant/conditioning fields, source nonbreakdown, or introduce a
  concrete machine model with a formal unit-roundoff cap.

  Canonical finite-max rational gamma cap route:
  `LSQRSolve.lean` now proves
  `storedQRCompactNormBudgetCoeffSmallness_of_source_den_ne_zero_uRationalGammaCanonicalBounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenURationalGammaCanonicalBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds`.
  These specialize the rational-gamma route further by choosing
  `Dcap = storedQRDiagDominantInvFactorBudget hmn A_hat` and
  `Ncap = storedQRPivotColumnNormBudget hmn A_hat`; the pointwise domination
  fields close by the finite-maximum lemmas.  Two weak-component passes are
  clean: repeated `git diff --check`, production Lean marker scans, focused
  LSQRSolve builds, executable lookup, qualified axiom audits, theorem PDF
  compile, targeted `pdftotext`, and rendered pages 194--196 passed.  The
  axiom audit reported only standard `propext`, `Classical.choice`, and
  `Quot.sound`.  Remaining positive progress must
  prove the primitive unit-roundoff cap, the displayed scalar cap inequality
  in these canonical maxima, local diagonal dominance/off-diagonal control,
  determinant/conditioning fields, source nonbreakdown, or introduce a concrete
  machine model with a formal unit-roundoff cap.

  Determinant-facing source nonbreakdown reduction:
  `LSQRSolve.lean` now proves
  `StoredQROffDiagonalControlInvariant.of_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds`.
  `LeastSquaresSketch.lean` now proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
  These wrappers close the next source-nonbreakdown dependency by deriving the
  positive trailing-norm field from nonzero previous/current leading-block
  determinants and the stored lower-zero shape, then reusing the signed-alpha
  source-nonbreakdown route.  Two weak-component passes are clean: focused
  LSQRSolve and LeastSquaresSketch builds, executable lookup, `git diff
  --check`, production marker scans, qualified axiom audits, theorem PDF
  compile, targeted `pdftotext`, and rendered pages 203--204 passed.  The axiom
  audits reported only standard `propext`, `Classical.choice`, and
  `Quot.sound`, and the temporary audit file was deleted.  Remaining positive
  progress must prove determinant nonzeroness, local diagonal
  dominance/off-diagonal control, scalar smallness, primitive unit-roundoff
  caps, conditioning fields, or a final concrete rectangular QR/preconditioner
  theorem under visible domain assumptions.

  Canonical scalar smallness route elimination:
  `LSQRSolve.lean` now proves
  `not_forall_diagDominant_sourceDen_uCap_implies_uRationalGammaCanonicalSmallness`.
  The theorem is a `1 x 1` exact-with-unit-roundoff witness showing that local
  diagonal dominance, source denominator nonbreakdown, `fp.u <= Ucap`, and
  `(m : ℝ) * Ucap < 1` do not imply the displayed canonical rational-gamma
  finite-max scalar smallness inequality.  Two weak-component passes are
  clean: repeated `git diff --check`, production Lean marker scans, focused
  LSQRSolve builds, executable lookup, qualified axiom audits, theorem PDF
  compile, targeted `pdftotext`, and rendered pages 198--199 passed.  The
  axiom audit reported only standard `propext`, `Classical.choice`, and
  `Quot.sound`.  This corrects the theorem statement for the bottleneck:
  positive progress on this branch must either keep the scalar inequality
  visible or prove it from stronger scale, conditioning, or concrete
  machine-model assumptions.
  Remaining positive progress must prove source nonbreakdown, local diagonal
  dominance/off-diagonal control, determinant/conditioning fields, a primitive
  unit-roundoff cap for a concrete model, or a positive scalar-smallness route
  under additional hypotheses.

  Actual unit-roundoff scalar-smallness route elimination:
  `LSQRSolve.lean` also proves
  `not_forall_diagDominant_sourceDen_actualU_implies_uRationalGammaCanonicalSmallness`.
  This companion removes the displayed cap notation and substitutes the actual
  `fp.u` into the rational-gamma scalar expression.  The same `1 x 1`
  exact-with-unit-roundoff style witness still falsifies the canonical
  finite-max scalar inequality under diagonal dominance, source nonbreakdown,
  and `m * fp.u < 1`.  This is another theorem-statement correction for the
  red bottleneck: positive progress must prove the scalar inequality from
  stronger scale/conditioning assumptions or keep it visible; it cannot be
  obtained merely by setting `Ucap = fp.u`.

  Source nonbreakdown reduction for canonical rational-gamma route:
  `LSQRSolve.lean` now proves
  `storedQRSourceDenominator_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos`,
  `StoredQROffDiagonalControlInvariant.of_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds`, and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds`.
  `LeastSquaresSketch.lean` now proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
  These derive the raw Householder source denominator from signed-alpha source
  facts and positive trailing norm squares, then reuse the existing canonical
  route.  Two weak-component passes are clean: repeated `git diff --check`,
  production Lean marker scans, focused LSQRSolve and LeastSquaresSketch
  builds, executable lookup, qualified axiom audit, theorem PDF compile,
  targeted `pdftotext`, and rendered page inspection passed.  The axiom audit
  reported only standard `propext`, `Classical.choice`, and `Quot.sound`, and
  the temporary audit file was deleted.  Remaining positive progress must prove
  positive trailing norms for the concrete loop, local diagonal
  dominance/off-diagonal control, determinant/conditioning fields, a primitive
  unit-roundoff cap for a concrete model, or a positive scalar-smallness route
  under stronger assumptions.

  Solver/probability handoff for canonical finite-max rational gamma route:
  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds`,
  and `LeastSquaresSketch.lean` now proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
  These compose the canonical source-denominator cap route into the stored-QR
  backward-error certificate and the high-probability rounded sampled-row
  objective theorem.  Two weak-component passes are clean: repeated
  `git diff --check`, production Lean marker scans, focused LSQRSolve and
  LeastSquaresSketch builds, executable lookup, qualified axiom audits,
  theorem PDF compile, targeted `pdftotext`, and rendered pages 195--201
  passed.  The axiom audit reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`.  Remaining positive progress must
  prove the primitive unit-roundoff cap, the displayed scalar cap inequality
  in these canonical maxima, local diagonal dominance/off-diagonal control,
  determinant/conditioning fields, source nonbreakdown, or introduce a concrete
  machine model with a formal unit-roundoff cap.

  Signed-alpha-definition invariant-surface reduction:
  `LSQRSolve.lean` now proves
  `StoredQROffDiagonalControlInvariant.of_diagDominant_signedAlphaDef_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds`.
  This closes a small listed theorem-surface dependency by deriving the
  squared-alpha identity and sign-choice inequality from the concrete
  `signedHouseholderAlpha` definition before reusing the determinant-facing
  canonical source-nonbreakdown route.  The determinant-facing solver theorem
  now syntactically consumes this packaged invariant through the generic
  off-diagonal-control handoff.  Two focused weak-component passes after this
  proof rewrite are clean: repeated focused LSQRSolve builds, executable lookup,
  `git diff --check`, production marker scans, qualified axiom audits for both
  the invariant and consuming solver theorem, theorem PDF compiles, targeted
  `pdftotext`, and rendered pages 203--204 passed.  The axiom audits reported
  only standard `propext`, `Classical.choice`, and `Quot.sound`, and the
  temporary axiom-audit file was deleted after the second pass.
  Remaining positive progress must prove determinant nonzeroness, local
  diagonal dominance/off-diagonal control, scalar smallness, primitive
  unit-roundoff caps, conditioning fields, or a final concrete rectangular
  QR/preconditioner theorem under visible domain assumptions.

  Current leading-block determinant reduction:
  `LSQRSolve.lean` now proves
  `StoredQROffDiagonalControlInvariant.of_diagDominant_signedAlphaDef_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds`.
  `LeastSquaresSketch.lean` now proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
  These wrappers derive the current leading-block determinant from
  `IsDiagDominantUpper` via `det_ne_zero_of_diagDominantUpper`, leaving only the
  previous transposed leading-block determinant visible on this route.  Two
  focused weak-component passes are clean: focused LSQRSolve and
  LeastSquaresSketch builds, executable lookup, `git diff --check`, production
  marker scans, qualified axiom audits, theorem PDF compile, targeted
  `pdftotext`, and rendered page 204 passed.  The axiom audits reported only
  standard `propext`, `Classical.choice`, and `Quot.sound`, and the temporary
  audit file was deleted.  Remaining positive progress must prove or classify
  previous transposed leading-block determinant nonzeroness, local diagonal
  dominance/off-diagonal control, scalar smallness, primitive unit-roundoff
  caps, conditioning fields, or a final concrete rectangular QR/preconditioner
  theorem under visible domain assumptions.

  Previous transposed leading-block determinant reduction:
  `LSQRSolve.lean` now proves
  `qrPreviousLeadingBlockTranspose_det_ne_zero_of_diagDominant_leadingBlock`,
  `StoredQROffDiagonalControlInvariant.of_diagDominant_signedAlphaDef_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds`,
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds`.
  `LeastSquaresSketch.lean` now proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
  These wrappers derive the previous transposed leading-block determinant from
  the top-left part of the same `IsDiagDominantUpper` leading block, leaving the
  previous lower-zero shape visible for the trailing-norm bridge.  Two focused
  weak-component passes are clean: repeated LSQRSolve and LeastSquaresSketch
  builds, executable lookup, `git diff --check`, production marker scans,
  qualified axiom audits, theorem PDF compile, targeted `pdftotext`, and
  rendered pages 205--206 passed.  The axiom audits reported only standard
  `propext`, `Classical.choice`, and `Quot.sound`, and the temporary audit file
  was deleted after validation.  Remaining positive progress must prove or
  classify local diagonal dominance/off-diagonal control, previous lower-zero
  shape, scalar smallness, primitive unit-roundoff caps, conditioning fields, or
  a final concrete rectangular QR/preconditioner theorem under visible domain
  assumptions.

  Previous-column lower-zero reduction:
  `LSQRSolve.lean` now proves
  `storedQRPreviousColumnLowerZero_of_stored_trailing_householder_sequence` and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds`;
  `LeastSquaresSketch.lean` now proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
  These wrappers derive the previous-column lower-zero field from the stored
  Householder panel recurrence via
  `fl_householderStoredPanel_sequence_prefix_lower_zero`.  Two focused
  weak-component passes are clean: focused LSQRSolve and LeastSquaresSketch
  builds, executable lookup, `git diff --check`, production marker scans,
  qualified axiom audits, theorem PDF compile, targeted `pdftotext`, and
  rendered pages 205--206 passed.  The axiom audits reported only standard
  `propext`, `Classical.choice`, and `Quot.sound`.  Remaining positive
  progress must prove or classify local diagonal dominance/off-diagonal
  control, scalar smallness, primitive unit-roundoff caps, conditioning fields,
  or a final concrete rectangular QR/preconditioner theorem under visible
  domain assumptions.

  Unit-roundoff-cap nonnegativity reduction:
  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_uCap`;
  `LeastSquaresSketch.lean` now proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_uCap`.
  These wrappers derive the former `0 <= Ucap` field from `FPModel.u_nonneg`
  and `fp.u <= Ucap`, then reuse the stored-lower route above.  Two focused
  weak-component passes are clean: focused LSQRSolve and LeastSquaresSketch
  builds, executable lookup, `git diff --check`, production marker scans,
  qualified axiom audit, theorem PDF compile, targeted `pdftotext`, and
  rendered pages 205--207 passed.  The axiom audit reported only standard
  `propext`, `Classical.choice`, and `Quot.sound`.  Remaining positive progress
  must prove or classify local diagonal dominance/off-diagonal control, scalar
  smallness, the primitive unit-roundoff cap itself, conditioning fields, or a
  final concrete rectangular QR/preconditioner theorem under visible domain
  assumptions.

  Cap-derived gamma-validity reduction:
  `Rounding.lean` now proves `gammaValid_of_u_le_cap`.  `LSQRSolve.lean` and
  `LeastSquaresSketch.lean` now prove
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_uCap_no_gammaValid` and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_uCap_no_gammaValid`.
  These wrappers derive the former `gammaValid fp m`/`gammaValid fp s` guard
  from `fp.u <= Ucap` and the displayed cap smallness, then derive the
  triangular-dimension guard by `gammaValid_mono`.  Two focused
  weak-component passes are clean: Rounding, LSQRSolve, and LeastSquaresSketch
  builds, executable lookup, `git diff --check`, touched-source marker scan,
  qualified axiom audit, theorem PDF compile, targeted `pdftotext`, and
  rendered pages 206--207 passed.  The only Lean warnings were the pre-existing
  `HouseholderQR` unused-variable warnings, and the axiom audit reported only
  standard `propext`, `Classical.choice`, and `Quot.sound`.  Remaining positive
  progress must prove or classify local diagonal dominance/off-diagonal
  control, scalar smallness, the primitive unit-roundoff cap itself,
  conditioning fields, or a final concrete rectangular QR/preconditioner
  theorem under visible domain assumptions.

  Actual-unit-roundoff stored-lower specialization:
  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_actualUnitRoundoff`;
  `LeastSquaresSketch.lean` now proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_actualUnitRoundoff`.
  These wrappers specialize the displayed cap to `Ucap = fp.u`, discharge
  `fp.u <= Ucap` by reflexivity, and state scalar smallness directly with the
  actual unit roundoff.  Two weak-component passes are clean: focused
  LSQRSolve and LeastSquaresSketch builds; executable lookup;
  `git diff --check`; touched Lean-source marker scan; qualified axiom audit;
  theorem PDF compile; targeted `pdftotext` over pages 206--208; and rendered
  pages 206--208 passed.  The only Lean warnings were the pre-existing
  `HouseholderQR` unused-variable warnings, and the axiom audit reported only
  standard `propext`, `Classical.choice`, and `Quot.sound`.  Remaining positive
  progress must prove or classify local diagonal dominance/off-diagonal
  control, scalar smallness, conditioning fields, or a final concrete
  rectangular QR/preconditioner theorem under visible domain assumptions.

  Actual-unit-roundoff scalar-validity guard:
  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_actualUnitRoundoff_no_gammaValid`;
  `LeastSquaresSketch.lean` now proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_actualUnitRoundoff_no_gammaValid`.
  These wrappers replace the remaining `gammaValid` guard on the actual-`u`
  route by the displayed scalar condition `(m : ℝ) * fp.u < 1` in the solver
  theorem and `(s : ℝ) * fp.u < 1` in the probability theorem, deriving
  operation validity internally from the cap-validity theorem with
  `Ucap = fp.u`.  Two weak-component passes are clean: focused LSQRSolve and
  LeastSquaresSketch builds, executable lookup, `git diff --check`, touched
  Lean-source marker scan, qualified axiom audit, theorem PDF compile, targeted
  `pdftotext` over pages 207--210, and rendered pages 207--208 passed.  The only
  Lean warnings were the pre-existing `HouseholderQR` unused-variable warnings,
  and the axiom audit reported only standard `propext`, `Classical.choice`, and
  `Quot.sound`.  This closes a listed hypothesis-surface dependency only; scalar
  smallness, local diagonal dominance/off-diagonal control, conditioning fields,
  and the final generic rectangular QR/preconditioner theorem remain open or
  visible.

  Signed-alpha scalar-smallness route elimination after validity reduction:
  `LSQRSolve.lean` now proves
  `not_forall_diagDominant_signedAlphaDef_sourceDen_actualU_no_gammaValid_implies_uRationalGammaCanonicalSmallness`,
  reusing the signed-alpha exact-unit-roundoff witness
  `not_forall_diagDominant_signedAlphaDef_sourceDen_actualU_implies_uRationalGammaCanonicalSmallness`
  but removing the abstract `gammaValid` premise.  This rules out the shortcut
  that the post-LS.2g-gc scalar validity guard `(m : ℝ) * fp.u < 1`, local
  diagonal dominance, the concrete signed-alpha equation, and source
  denominator nonbreakdown automatically imply the canonical finite-max
  rational-gamma scalar smallness inequality.  Two weak-component passes are
  clean: focused LSQRSolve and LeastSquaresSketch builds, executable lookup,
  `git diff --check`, touched Lean-source marker scan, qualified axiom audit,
  theorem PDF compile, targeted `pdftotext` over pages 207--209, and rendered
  page 208 passed.  The only Lean warnings were the pre-existing `HouseholderQR`
  unused-variable warnings, and the axiom audit reported only standard
  `propext`, `Classical.choice`, and `Quot.sound`.  This is a listed
  scalar-smallness route elimination only; future progress must prove scalar
  smallness from stronger scale/conditioning or concrete machine-model
  assumptions, prove/classify local diagonal-dominance/off-diagonal-control or
  conditioning fields, or keep those hypotheses visible in a final
  QR/preconditioner theorem.

  Actual-unit-roundoff scalar-validity guard for row-max-defect route:
  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowMaxDiagDefect_globalProduct_of_actualUnitRoundoff_no_gammaValid`;
  `LeastSquaresSketch.lean` now proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowMaxDiagDefect_globalProduct_solver_of_actualUnitRoundoff_no_gammaValid`.
  These wrappers put the scalar row-max-defect/global-product equation (8)
  route on the same actual-unit-roundoff validity surface as the stored-lower
  branch: `(m : ℝ) * fp.u < 1` derives the local solver `gammaValid` guards,
  and `(s : ℝ) * fp.u < 1` derives the sampled probability guards.  Two
  weak-component passes are clean: focused LSQRSolve and LeastSquaresSketch
  builds, executable lookup, `git diff --check`, touched Lean-source marker
  scan, qualified axiom audit, theorem PDF compile, targeted `pdftotext` over
  page 182, and rendered page 182 passed.  The only Lean warnings were the
  pre-existing `HouseholderQR` unused-variable warnings, and the axiom audit
  reported only standard `propext`, `Classical.choice`, and `Quot.sound`.  This
  closes only a validity-surface dependency for a visible-domain
  row-max-defect theorem; it does not prove the scalar
  defect/off-diagonal-control condition, determinant or norm-square
  nonbreakdown fields, global compact-product smallness, conditioning fields,
  or the final generic rectangular QR/preconditioner theorem.

  Finite stage-diagonal lower-bound packaging for the active/prefix route:
  `LSQRSolve.lean` now defines `storedQRStageDiagLowerDefectBudget`, proves
  `storedQRStageDiagLowerDefect_le_budget`, and proves
  `storedQRStageBudget_le_diag_of_stageDiagLowerDefectBudget_nonpos`.  The
  active/prefix source-control and solver wrappers with suffix
  `_globalCompactBudget_completedColumns_globalProduct_stageDiagDefect_offdiag_rows`
  consume the single scalar condition
  `storedQRStageDiagLowerDefectBudget hmn A_hat stageBudget <= 0` instead of
  the full pointwise diagonal lower-bound family
  `stageBudget k <= |(S_k)_{ii}|` for every displayed off-diagonal row `i < k`.
  This is an admissible red-bottleneck dependency reduction: it packages a
  listed diagonal-lower-bound obligation as one finite scalar check.  It does
  not prove that scalar condition from the Cox--Higham pivoted/sorted loop, and
  it does not close determinant/norm-square nonbreakdown, global compact-product
  smallness, or the final QR/preconditioner theorem.  Remaining positive
  progress must prove the scalar stage-diagonal condition from a concrete
  pivoted/sorted/off-diagonal-controlled recurrence, prove the determinant and
  nonbreakdown/product-smallness fields, or keep those fields visibly scoped as
  domain assumptions.

  Row-max-to-stage-diagonal scalar bridge:
  `LSQRSolve.lean` now proves
  `storedQRStageDiagLowerDefectBudget_nonpos_of_rowMaxDiagDefectBudget_nonpos_stageBudget_le_rowMax`
  and
  `storedQRStageDiagLowerDefectBudget_nonpos_of_diagDominant_stageBudget_le_rowMax`.
  These adapters close a small listed packaging gap between the row-max branch
  and the active/prefix stage-budget branch: if the uniform stage budget is no
  larger than each displayed strict-upper row maximum on the rows `i < k`,
  then a nonpositive row-max defect, or local diagonal dominance via the
  existing row-max theorem, implies
  `storedQRStageDiagLowerDefectBudget <= 0`.  This does not prove the needed
  stage-budget/row-max comparison for a concrete pivoted loop; it only prevents
  the scalar stage-diagonal condition from being re-proved once such row-max
  data are available.

  Stage-budget/row-max comparison route elimination:
  `LSQRSolve.lean` now proves
  `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageBudget_le_rowMax`.
  The same active-pivot finite sequence used for the row-budget diagonal
  obstruction satisfies upper triangular nonsingular displayed blocks,
  positive active-block mass, active max-pivoting, active-block budget control,
  and displayed strict-upper budget control when the uniform stage budget is
  the constant `3`.  At displayed stage one, however, the strict-upper row
  maximum is only `2`, so the comparison `stageBudget <= rowMax` fails.  This
  rules out deriving the LS.2g-gi bridge's remaining comparison from the
  current active-pivot/budget surface.  Positive progress must therefore prove
  a stronger pivoted/sorted/off-diagonal-control invariant that actually
  compares the chosen stage budget with displayed row maxima, or keep that
  comparison visible as a source/domain assumption.

  Active-max-pivot stage-diagonal reduction:
  `LSQRSolve.lean` now proves `storedQRActiveMaxPivotColumn_pivotMax` and the
  active-pivot-policy source-control/solver wrappers with suffix
  `_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_stageDiagDefect_offdiag_rows`.
  These theorems compose the finite scalar stage-diagonal condition
  `storedQRStageDiagLowerDefectBudget <= 0` with the policy equation that the
  displayed pivot is `householderActiveMaxPivotColumn`, deriving the raw
  pivot-maximality inequality internally.  This closes a listed pivot-policy
  field on the newest scalar stage-diagonal route.  It still does not prove the
  scalar stage-diagonal condition, determinant/nonbreakdown or conditioning
  fields, compact-product smallness, or the final QR/preconditioner theorem.

  Visible row-max-assumption active-pivot surface:
  `LSQRSolve.lean` now proves the active-pivot source-control and solver
  wrappers with suffix
  `_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageBudgetLeRowMax_offdiag_rows`.
  These theorems consume a nonpositive
  `storedQRRowMaxDiagDefectBudget` assumption plus the explicit displayed-row
  comparison
  `stageBudget k <= qrLeadingStrictUpperRowMaxBudget hmn A_hat k hk i`, derive
  `storedQRStageDiagLowerDefectBudget <= 0` through the row-max bridge, and
  then reuse the active-pivot stage-diagonal route.  This is a theorem-surface
  correction and dependency reduction only: the row-max scalar defect, the
  stage-budget/row-max comparison, determinant/nonbreakdown or conditioning
  fields, compact-product smallness, and the final QR/preconditioner theorem
  remain open or visible.

  Active-pivot row-max scalar-defect route elimination:
  `LSQRSolve.lean` now proves
  `activeMaxPivotRowBudgetDiagCounterexample_rowMaxDiagDefectBudget_pos` and
  `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_rowMaxDiagDefectBudget_nonpos`.
  The same finite active-pivot sequence used in the row-budget and
  stage-budget/row-max obstructions has displayed strict-upper row maximum `2`
  and displayed diagonal magnitude `1` at stage one, so its finite row-max
  scalar defect is positive.  Upper triangular nonsingular displayed blocks,
  positive active-block mass, active max-pivoting, nonnegative active-block
  budgets, active-block budget control, and displayed strict-upper budget
  control therefore do not imply
  `storedQRRowMaxDiagDefectBudget <= 0`.  Positive progress must prove this
  scalar row-max condition from a stronger pivoted/sorted/off-diagonal-control
  invariant, or keep it as a visible source/domain assumption.

  Product-smallness/row-max cross-route elimination:
  `LSQRSolve.lean` now proves
  `not_forall_upper_tri_det_ne_zero_product_budget_implies_rowMaxDiagDefectBudget_nonpos`.
  The same active-pivot row-budget counterexample sequence, with compact budget
  `B = 1/16`, satisfies upper-triangular nonsingular displayed leading-block
  hypotheses and the compact-product inequality, but the finite row-max defect
  remains positive at displayed stage one.  Therefore compact-product
  smallness cannot discharge the row-max defect condition left by the visible
  row-max route.

  Product-smallness/active-budget row-max route elimination:
  `LSQRSolve.lean` now proves
  `not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_rowMaxDiagDefectBudget_nonpos`.
  Adding the compact-product inequality to the active-pivot active/off-diagonal
  budget surface still leaves the same row-max scalar defect witness: with
  compact budget `B = 1/16`, the row maximum at displayed stage one is `2`
  while the displayed diagonal magnitude is `1`.

  Product-smallness/stage-diagonal scalar route elimination:
  `LSQRSolve.lean` now proves
  `activeMaxPivotRowBudgetDiagCounterexample_stageDiagLowerDefectBudget_pos`
  and
  `not_forall_upper_tri_det_ne_zero_product_budget_implies_stageDiagLowerDefectBudget_nonpos`.
  With compact budget `B = 1/16` and constant stage budget `2`, the same
  active-pivot witness satisfies the product-smallness side but has positive
  scalar stage-diagonal defect.  Product smallness cannot discharge the
  active/prefix diagonal lower-bound scalar condition.

  Product-smallness/active-budget stage-diagonal route elimination:
  `LSQRSolve.lean` now proves
  `not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageDiagLowerDefectBudget_nonpos`.
  With compact budget `B = 1/16` and constant stage budget `2`, the same
  active-pivot witness satisfies product-smallness and active/off-diagonal
  budget hypotheses, but the scalar stage-diagonal defect is positive.

  Active-pivot budget scalar stage-diagonal route elimination:
  `LSQRSolve.lean` now proves
  `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageDiagLowerDefectBudget_nonpos`.
  If the active-pivot active/off-diagonal budget surface alone implied the
  scalar stage-diagonal condition, then the product-plus-active surface would
  imply it too; the preceding counterexample refutes that stronger universal
  statement.

  Finite stage-diagonal converse packaging:
  `LSQRSolve.lean` now proves
  `storedQRStageDiagLowerDefectBudget_nonpos_of_stageBudget_le_diag`.
  This is the converse of the scalar extractor: a pointwise displayed
  diagonal lower-bound family `stageBudget k <= |(S_k)_{ii}|` for every
  off-diagonal row `i < k` makes
  `storedQRStageDiagLowerDefectBudget hmn A_hat stageBudget <= 0`.
  Together with the extractor theorem, the finite scalar condition is now an
  exact package for that displayed family.  The concrete loop still has to
  prove the family, derive it via row-max data, or keep it visible.

  Finite stage-budget/row-max comparison packaging:
  `LSQRSolve.lean` now defines
  `storedQRStageRowMaxComparisonDefectBudget` and proves the extractor,
  converse, and scalar bridge theorems
  `storedQRStageBudget_le_rowMax_of_stageRowMaxComparisonDefectBudget_nonpos`,
  `storedQRStageRowMaxComparisonDefectBudget_nonpos_of_stageBudget_le_rowMax`,
  and
  `storedQRStageDiagLowerDefectBudget_nonpos_of_rowMaxDiagDefectBudget_nonpos_stageRowMaxComparisonDefectBudget_nonpos`.
  The displayed comparison `stageBudget k <= rowMax(k,i)` is therefore now a
  scalar finite maximum condition over exactly the off-diagonal rows `i < k`.
  This closes only the comparison-package direction; the concrete loop still
  has to prove the scalar comparison defect, derive it from stronger
  pivoted/sorted/off-diagonal-control data, or keep it visible.

  Product-smallness/active-budget comparison route elimination:
  `LSQRSolve.lean` now proves
  `not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageBudget_le_rowMax`.
  Adding the compact-product inequality to the active-pivot active/off-diagonal
  budget surface still leaves the same oversized-budget witness: stage budget
  `3` controls the active and displayed strict-upper entries, but the displayed
  row maximum at stage one is `2`, so the comparison fails.

  Probability-level visible row-max active-pivot equation (8) surface:
  `LeastSquaresSketch.lean` now proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver`.
  This theorem pushes the visible row-max surface from the local QR solver up
  to the high-probability rounded sampled-row least-squares objective theorem:
  samplewise `storedQRRowMaxDiagDefectBudget <= 0` plus
  `stageBudget <= qrLeadingStrictUpperRowMaxBudget` derive the pointwise
  diagonal lower-bound family internally, and the result then reuses the
  active-max-pivot probability wrapper.  This closes a theorem-surface
  mismatch only.  The red bottleneck still requires a proof, stronger domain
  invariant, or visible assumption for row-max defect, the stage-budget/row-max
  comparison, determinant/nonbreakdown or conditioning fields, and global
  compact-product smallness.
  Its horizon-clamped sibling
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_horizonBudget`
  performs the same row-max reduction, then reuses LS.2g-ia, removing the
  samplewise global budget-monotonicity field from this visible row-max
  probability surface.  Full validation is clean for that sibling: focused
  RandNLA least-squares build, executable lookup, standard-only axiom audit,
  two theorem-PDF compiles to 271 pages, rendered inspection of pages 228, 229,
  and 269, broad `lake build`, whitespace check, marker scan, and
  temporary-file cleanup all passed.

  Actual-unit-roundoff validity surface for the probability-level visible
  row-max active-pivot equation (8) theorem: `LeastSquaresSketch.lean` now
  proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid`.
  This removes the sampled `gammaValid fp s` and triangular `gammaValid fp n`
  hypotheses from the LS.2g-gm wrapper, replacing them by the scalar guard
  `(s : ℝ) * fp.u < 1`.  The proof derives the two validity fields with
  `gammaValid_of_u_le_cap` and `gammaValid_mono`.  This closes only the
  validity-surface dependency for the visible row-max probability theorem; the
  row-max defect, stage-budget/row-max comparison, determinant/nonbreakdown or
  conditioning fields, and compact-product smallness remain visible or open.
  The actual-unit horizon sibling
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageBudgetLeRowMax_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget`
  combines this scalar validity guard with LS.2g-ib, so the row-max
  actual-unit probability surface no longer exposes global budget monotonicity
  either.  Full validation is clean for that sibling: focused RandNLA
  least-squares build, executable lookup, standard-only axiom audit, two
  theorem-PDF compiles to 272 pages, whole-PDF text extraction, rendered
  inspection of pages 228, 229, 230, and 269, broad `lake build`, whitespace
  check, marker scan, and temporary-file cleanup all passed.

  Local actual-unit-roundoff validity surface for the visible row-max
  active-pivot solver theorem: `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageBudgetLeRowMax_offdiag_rows_of_actualUnitRoundoff_no_gammaValid`.
  This removes the local `gammaValid fp m` and triangular `gammaValid fp n`
  hypotheses from the LS.2g-gk solver wrapper, replacing them by the scalar
  guard `(m : ℝ) * fp.u < 1`.  The proof derives the two validity fields with
  `gammaValid_of_u_le_cap` and `gammaValid_mono`, then calls the existing
  visible row-max active-pivot solver theorem.  This closes only the local
  validity-surface dependency; the row-max scalar defect, the displayed
  stage-budget/row-max comparison, determinant/nonbreakdown or conditioning
  fields, dual compact-budget data, and compact-product smallness remain
  visible or open.

  Source-control actual-unit-roundoff validity surface for the visible row-max
  active-pivot route: `LSQRSolve.lean` now also proves
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_rowMaxDiagDefect_stageBudgetLeRowMax_offdiag_rows_of_actualUnitRoundoff_no_gammaValid`.
  This removes the local `gammaValid fp m` hypothesis from the source-control
  theorem itself, replacing it by the scalar guard `(m : ℝ) * fp.u < 1`.  The
  proof derives validity with `gammaValid_of_u_le_cap`, then calls the existing
  visible row-max source-control theorem.  This closes only the source-level
  validity-surface dependency; the row-max scalar defect, the displayed
  stage-budget/row-max comparison, determinant/nonbreakdown or conditioning
  fields, dual compact-budget data, and compact-product smallness remain
  visible or open.

  Exact no-pivot stage-diagonal scalar route elimination:
  `LSQRSolve.lean` now proves
  `exactHouseholderQRDiagDominanceCounterexample_stageDiagLowerDefectBudget_pos`
  and
  `not_forall_exact_trailing_householder_sequence_implies_stageDiagLowerDefectBudget_nonpos`.
  The same two-stage exact no-pivot Householder recurrence used for the
  diagonal-dominance and row-max obstructions has positive
  `storedQRStageDiagLowerDefectBudget` when the stage budget is the constant
  sequence `2`; hence exact recurrence, valid signed squared-norm identities,
  and nonzero Householder denominators do not imply
  `storedQRStageDiagLowerDefectBudget <= 0`.  This rules out the naive shortcut
  for the remaining scalar stage-diagonal field.  Positive progress must now
  come from a genuinely stronger pivoted/sorted/off-diagonal-controlled loop
  invariant, determinant/nonbreakdown and conditioning proofs, scalar
  compact-product smallness, or a final theorem with those assumptions visibly
  scoped.

  Exact no-pivot comparison scalar route elimination:
  `LSQRSolve.lean` now proves
  `exactHouseholderQRDiagDominanceCounterexample_stageRowMaxComparisonDefectBudget_pos`
  and
  `not_forall_exact_trailing_householder_sequence_implies_stageRowMaxComparisonDefectBudget_nonpos`.
  The same exact two-stage no-pivot Householder recurrence witness has positive
  `storedQRStageRowMaxComparisonDefectBudget` for the constant stage budget
  `3`: at displayed stage one, the strict-upper row maximum is `2`.  Thus exact
  recurrence, valid signed squared-norm identities, nonzero Householder
  denominators, and nonnegative stage budgets cannot prove the comparison
  scalar.  Red dependency status change: the route "prove the comparison
  scalar from the ordinary exact no-pivot recurrence plus nonnegative stage
  budgets" is eliminated.  Positive progress must use a stronger
  pivoted/sorted/off-diagonal-controlled invariant or keep the scalar
  comparison field visible.

  Active scalar-comparison source-denominator compact-product handoff:
  `LSQRSolve.lean` now proves
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows`.
  These local wrappers derive the active branch's raw compact-product
  hypothesis from the canonical source-denominator rational-gamma finite-max
  theorem and the per-pivot product budget.  Red dependency status change: the
  assembled finite-max compact-product scalar involving
  `storedQRCompactSequenceRelativeBudget` is reduced, on this local
  source-control/solver branch, to source-denominator nonbreakdown,
  `fp.u <= Ucap`, `(m : ℝ) * Ucap < 1`, and the canonical rational-gamma
  cap-smallness inequality.  The remaining red dependencies are local
  diagonal dominance or equivalent off-diagonal control, the scalar comparison
  defect, active-pivot policy, signed-stage recurrence budgets,
  source-denominator/unit-cap/cap-smallness obligations, and the final concrete
  QR/preconditioner theorem.

  Sampled active scalar-comparison source-denominator compact-product handoff:
  `LeastSquaresSketch.lean` now proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver`.
  The sampled theorem applies the LS.2g-hm source-control certificate per
  trace and then reuses the generic source-off-diagonal-control equation (8)
  theorem.  Red dependency status change: the assembled finite-max
  compact-product scalar is reduced at the probability level as well, leaving
  source-denominator nonbreakdown, `fp.u <= Ucap`, `(s : ℝ) * Ucap < 1`, and
  the canonical rational-gamma cap-smallness inequality visible on the sampled
  active branch.  The remaining red dependencies are local diagonal dominance
  or equivalent off-diagonal control, the scalar comparison defect,
  active-pivot policy, signed-stage recurrence budgets,
  source-denominator/unit-cap/cap-smallness obligations, and the final concrete
  QR/preconditioner theorem.

  Active source-denominator actual-unit validity surface:
  `LSQRSolve.lean` now proves the source-control and solver wrappers
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid`;
  `LeastSquaresSketch.lean` now proves the probability wrapper
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid`.
  Red dependency status change: the sampled and local active source-denominator
  surfaces no longer expose an auxiliary unit-roundoff cap or abstract
  `gammaValid` field.  They use `Ucap = fp.u`, `FPModel.u_nonneg`,
  `gammaValid_of_u_le_cap`, and `gammaValid_mono` to derive validity from
  `(m : ℝ) * fp.u < 1` or `(s : ℝ) * fp.u < 1`.  The remaining red
  dependencies are source-denominator nonbreakdown, actual-unit scalar
  cap-smallness, local diagonal dominance or equivalent off-diagonal control,
  the scalar comparison defect, active-pivot policy, signed-stage recurrence
  budgets, and the final concrete QR/preconditioner theorem.

  Active stored-lower source-denominator nonbreakdown reduction:
  `LSQRSolve.lean` now proves
  `storedQRSourceDenominator_ne_zero_of_diagDominant_signedAlphaDef_stored_trailing_sequence`,
  deriving the raw Householder source denominator from the stored panel
  recurrence, signed-alpha definition, and local diagonal dominance.  The
  active actual-unit source-control and solver wrappers
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_storedLower_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_actualUnitRoundoff_no_gammaValid`,
  plus the sampled wrapper
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid`,
  use that helper to remove the raw denominator field from the active
  actual-unit branch.  Red dependency status change: source-denominator
  nonbreakdown is closed for this stored-lower actual-unit surface.  The
  remaining red dependencies are actual-unit scalar cap-smallness, local
  diagonal dominance or equivalent off-diagonal control, the scalar comparison
  defect, active-pivot policy, signed-stage recurrence budgets, and the final
  concrete QR/preconditioner theorem.

  Stored-recurrence actual-unit scalar-smallness route elimination:
  `LSQRSolve.lean` now proves
  `not_forall_diagDominant_signedAlphaDef_stored_trailing_sequence_actualU_no_gammaValid_implies_uRationalGammaCanonicalSmallness`.
  This adapts the earlier signed-alpha scalar-smallness obstruction to the
  post-stored-lower surface: the witness satisfies the actual stored panel
  recurrence, local diagonal dominance, the signed-alpha equation, and
  `(1 : ℝ) * fp.u < 1`, but the canonical rational-gamma finite-max scalar
  smallness inequality still fails.  Red dependency status change: the route
  "derive actual-unit scalar smallness from stored recurrence plus local
  diagonal dominance and signed-alpha facts" is eliminated.  Scalar smallness
  must come from stronger scale/conditioning or concrete machine-model
  hypotheses, or remain visible in the final QR/preconditioner theorem.

  Stored-recurrence actual-unit diagonal-dominance route elimination:
  `LSQRSolve.lean` now proves
  `exactHouseholderQRDiagDominanceCounterexample_stored_step`,
  `exactHouseholderQRDiagDominanceCounterexample_signed_alpha_def`, and
  `not_forall_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_implies_diagDominant`.
  This lifts the earlier `2 x 2` exact no-pivot diagonal-dominance witness to
  the stored-lower actual-unit surface: under an exact FP model with
  `fp.u = 0`, the witness satisfies the stored panel recurrence, signed-alpha
  equation, nonzero source denominators, and `(2 : ℝ) * fp.u < 1`, but the
  final triangular block is still not diagonally dominant.  Red dependency
  status change: the route "derive local diagonal dominance/off-diagonal
  control from stored recurrence plus signed-alpha, source-denominator, and
  actual-unit validity facts" is eliminated.  A positive theorem must supply a
  stronger pivoted/sorted/off-diagonal-control invariant or keep local
  diagonal dominance visible.

  Stored-recurrence actual-unit active-pivot route elimination:
  `LSQRSolve.lean` now proves
  `exactHouseholderQRDiagDominanceCounterexample_not_activeMaxPivotChoice` and
  `not_forall_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_implies_activeMaxPivotChoice`.
  The same `2 x 2` stored-recurrence witness starts from `[[1,2],[0,1]]`.
  At stage zero, the second column has active trailing norm square `5`, while
  the displayed first pivot has active trailing norm square `1`; therefore
  `householderActiveMaxPivotColumn_pivot_max` contradicts the displayed-pivot
  equation.  Red dependency status change: the route "derive active-pivot
  policy from stored recurrence plus signed-alpha, source-denominator, and
  actual-unit validity facts" is eliminated.  A positive theorem must prove a
  concrete pivoted/sorted pivot-selection invariant or keep the active-pivot
  equation visible.

  Stored-recurrence actual-unit scalar row-budget route elimination:
  `LSQRSolve.lean` now proves
  `not_forall_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_implies_stageDiagLowerDefectBudget_nonpos`
  and
  `not_forall_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
  The same `2 x 2` exact FP witness with `fp.u = 0` satisfies the stored panel
  recurrence, signed-alpha equation, nonzero source denominators, and
  `(2 : ℝ) * fp.u < 1`, but the constant stage budget `2` gives positive
  `storedQRStageDiagLowerDefectBudget`, and the nonnegative constant stage
  budget `3` gives positive `storedQRStageRowMaxComparisonDefectBudget`.  Red
  dependency status change: the routes "derive scalar diagonal lower-bound"
  and "derive scalar stage-budget/row-max comparison" from stored recurrence
  plus signed-alpha, source-denominator, and actual-unit validity facts are
  eliminated.  A positive theorem must prove those scalar fields from a
  stronger pivoted/sorted/off-diagonal-control invariant or keep them visible.

  Diagonal-dominant stored-recurrence actual-unit scalar row-budget route
  elimination:
  `LSQRSolve.lean` now proves
  `storedDiagDominantComparisonCounterexample_stored_step`,
  `storedDiagDominantComparisonCounterexample_diagDominant`,
  `not_forall_diagDominant_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageDiagLowerDefectBudget_nonpos`,
  and
  `not_forall_diagDominant_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
  The exact stored sequence starting from `[[3,2],[0,1]]` follows the stored
  panel recurrence under exact floating-point arithmetic with `fp.u = 0`,
  satisfies the signed-alpha equation, nonzero source denominators, `(2 : ℝ) *
  fp.u < 1`, local diagonal dominance, and nonnegative stage budgets.  Still,
  constant stage budgets `4` and `3` make the scalar stage-diagonal and
  stage-budget/row-max comparison defects positive.  Red dependency status
  change: the routes "derive scalar diagonal lower-bound" and "derive scalar
  stage-budget/row-max comparison" from stored recurrence plus diagonal
  dominance are eliminated.  A positive theorem must prove these scalar fields
  from a genuine loop invariant or keep them visible.

  Active-pivot diagonal-dominant stored-recurrence comparison route
  elimination:
  `LSQRSolve.lean` now proves
  `storedDiagDominantComparisonCounterexample_activeMaxPivotChoice` and
  `not_forall_diagDominant_activeMaxPivot_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
  The same stored sequence from `[[3,2],[0,1]]` satisfies the finite active
  max-pivot selector policy in addition to stored recurrence, signed-alpha
  equation, source-denominator facts, actual-unit validity, local diagonal
  dominance, and nonnegative stage budgets.  The scalar stage-budget/row-max
  comparison defect remains positive for constant stage budget `3`.  Red
  dependency status change: the stronger route "derive scalar comparison from
  diagonal-dominant stored recurrence plus active max-pivoting" is eliminated.
  A positive theorem must still prove the comparison scalar from a stronger
  pivoted/sorted/off-diagonal-control loop invariant or keep it visible.

  Compact-product active-pivot diagonal-dominant stored-recurrence comparison
  route elimination:
  `LSQRSolve.lean` now proves
  `storedDiagDominantComparisonCounterexample_rhs_step`,
  `storedDiagDominantComparisonCounterexample_compactSequenceRelativeBudget_eq_zero`,
  `storedDiagDominantComparisonCounterexample_compactSequenceProductBudget_lt_one`,
  and
  `not_forall_diagDominant_activeMaxPivot_product_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
  The same stored matrix sequence, paired with a zero RHS trace, satisfies the
  stored RHS recurrence and exact/zero-RHS global compact-product smallness in
  addition to the stored recurrence, signed-alpha equation, source-denominator
  facts, actual-unit validity, local diagonal dominance, active-pivot policy,
  and nonnegative stage budgets.  The scalar stage-budget/row-max comparison
  defect remains positive for constant stage budget `3`.  Red dependency
  status change: the stronger route "derive scalar comparison from
  diagonal-dominant stored recurrence plus active max-pivoting plus
  compact-product smallness" is eliminated.  A positive theorem must still
  prove the comparison scalar from a stronger pivoted/sorted/off-diagonal-control
  loop invariant or keep it visible.

  Finite-max active-pivot diagonal-dominant stored-recurrence comparison route
  elimination:
  `LSQRSolve.lean` now proves
  `storedDiagDominantComparisonCounterexample_finiteMaxSmallness` and
  `not_forall_diagDominant_activeMaxPivot_finiteMaxSmallness_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
  The exact/zero-RHS witness has zero compact relative budget, so the canonical
  finite-max compact-product scalar used by the active finite-max branch
  reduces to `0 < 1`; nevertheless the scalar stage-budget/row-max comparison
  defect remains positive for constant stage budget `3`.  Red dependency
  status change: the stronger route "derive scalar comparison from
  diagonal-dominant stored recurrence plus active max-pivoting plus canonical
  finite-max compact-product smallness" is eliminated.  A positive theorem
  must still prove the comparison scalar from a stronger
  pivoted/sorted/off-diagonal-control loop invariant or keep it visible.

  Signed-stage global-budget finite-max active-pivot diagonal-dominant
  stored-recurrence comparison route elimination:
  `LSQRSolve.lean` now proves
  `storedDiagDominantComparisonCounterexample_globalBudgetStageBudget_nonneg`,
  `storedDiagDominantComparisonCounterexample_globalCompactBudget_eq_zero`,
  `storedDiagDominantComparisonCounterexample_globalCompactBudget_recurrence`,
  `storedDiagDominantComparisonCounterexample_stageRowMaxComparisonDefectBudget_pos_globalBudgetStageBudget`,
  and
  `not_forall_diagDominant_activeMaxPivot_globalCompactBudget_finiteMaxSmallness_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
  The exact/zero-RHS witness uses the nonconstant nonnegative stage budget
  `0, 3, 10, ...`; the signed global compact-update budgets are zero, and
  `coxHighamActiveRowGrowthFactor 2 <= 3` supplies the only nontrivial
  recurrence step.  The scalar stage-budget/row-max comparison defect remains
  positive at stage one.  Red dependency status change: the stronger route
  "derive scalar comparison from diagonal-dominant stored recurrence plus
  active max-pivoting plus canonical finite-max compact-product smallness plus
  the signed-stage global compact-budget recurrence" is eliminated.  A
  positive theorem must still prove the comparison scalar from a stronger
  pivoted/sorted/off-diagonal-control loop invariant or keep it visible.

  Row-max-granted signed-stage global-budget finite-max active-pivot
  diagonal-dominant stored-recurrence comparison route elimination:
  `LSQRSolve.lean` now proves
  `storedDiagDominantComparisonCounterexample_rowMaxDiagDefectBudget_nonpos`
  and
  `not_forall_diagDominant_activeMaxPivot_globalCompactBudget_finiteMaxSmallness_rowMaxDiagDefect_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
  The exact/zero-RHS signed-stage witness also has
  `storedQRRowMaxDiagDefectBudget <= 0`, obtained from its local diagonal
  dominance, while the nonconstant stage budget `0, 3, 10, ...` still makes
  the scalar comparison defect positive at stage one.  Red dependency status
  change: the stronger route "derive scalar comparison from diagonal-dominant
  stored recurrence plus active max-pivoting plus row-max/diagonal defect
  control plus canonical finite-max compact-product smallness plus the
  signed-stage global compact-budget recurrence" is eliminated.  The scalar
  comparison invariant itself remains the red bottleneck.

  Determinant- and row-max-granted signed-stage global-budget finite-max
  active-pivot diagonal-dominant stored-recurrence comparison route
  elimination:
  `LSQRSolve.lean` now proves
  `storedDiagDominantComparisonCounterexample_leadingBlock_det_ne_zero`
  and
  `not_forall_diagDominant_activeMaxPivot_leadingBlock_det_ne_zero_globalCompactBudget_finiteMaxSmallness_rowMaxDiagDefect_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
  The exact/zero-RHS signed-stage witness also has nonsingular displayed
  leading blocks: determinant `3` at stage zero and determinant `-3` at stage
  one.  All row-max-granted signed-stage fields remain present, but the scalar
  comparison defect is still positive at stage one.  Red dependency status
  change: the stronger route "derive scalar comparison from diagonal-dominant
  stored recurrence plus active max-pivoting plus nonsingular displayed leading
  blocks plus row-max/diagonal defect control plus canonical finite-max
  compact-product smallness plus the signed-stage global compact-budget
  recurrence" is eliminated.  The scalar comparison invariant itself remains
  the red bottleneck.

  Conditioning- and row-max-granted signed-stage global-budget finite-max
  active-pivot diagonal-dominant stored-recurrence comparison route
  elimination:
  `LSQRSolve.lean` now proves
  `storedDiagDominantComparisonCounterexample_compactComponentBudget_eq_zero`,
  `storedDiagDominantComparisonCounterexampleKappaBudget`,
  `storedDiagDominantComparisonCounterexampleKappaNormSqBudget`,
  `storedDiagDominantComparisonCounterexample_kappaBudget_le`,
  `storedDiagDominantComparisonCounterexample_kappaNormSqBudget_pos`,
  `storedDiagDominantComparisonCounterexample_kappaNormSqBudget`,
  `storedDiagDominantComparisonCounterexample_dualBudget`, and
  `not_forall_diagDominant_activeMaxPivot_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_globalCompactBudget_finiteMaxSmallness_rowMaxDiagDefect_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonnegStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
  The exact/zero-RHS signed-stage witness also satisfies the local
  `kappaInf`/self-norm and dual compact-budget fields used by the
  conditioning branch: the exact compact component budget is zero, and the
  displayed `K` budget is chosen as the exact squared expression plus one.
  All determinant- and row-max-granted signed-stage fields remain present, but
  the scalar comparison defect is still positive at stage one.  Red dependency
  status change: the stronger route "derive scalar comparison from
  diagonal-dominant stored recurrence plus active max-pivoting plus nonsingular
  displayed leading blocks plus local conditioning/dual compact-budget data
  plus row-max/diagonal defect control plus canonical finite-max
  compact-product smallness plus the signed-stage global compact-budget
  recurrence" is eliminated.  The scalar comparison invariant itself remains
  the red bottleneck.

  LS.2g-im final-surface initial/global-product conditioning-granted
  scalar-comparison route elimination:
  `LSQRSolve.lean` now proves
  `storedDiagDominantComparisonCounterexampleFinalSurfaceStageBudget`,
  `storedDiagDominantComparisonCounterexample_finalSurfaceStageBudget_nonneg`,
  `storedDiagDominantComparisonCounterexample_finalSurfaceStageBudget_mono`,
  `storedDiagDominantComparisonCounterexample_finalSurface_init`,
  `storedDiagDominantComparisonCounterexample_finalSurface_initBlock`,
  `storedDiagDominantComparisonCounterexample_finalSurface_globalCompactBudget_recurrence`,
  `storedDiagDominantComparisonCounterexample_stageRowMaxComparisonDefectBudget_pos_finalSurfaceStageBudget`,
  and
  `not_forall_diagDominant_activeMaxPivot_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_init_globalProduct_globalCompactBudget_rowMaxDiagDefect_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonneg_monoStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
  The exact/zero-RHS signed-stage witness now uses the final-surface budget
  `B_0 = 3`, `B_1 = 10`, and `B_k = 30` for later indices.  This budget
  satisfies the initial full-block and displayed row-budget fields, is
  nonnegative and monotone, and still satisfies the exact signed-stage global
  compact-budget recurrence and global compact-product smallness.  Together
  with diagonal dominance, active pivoting, nonsingular displayed leading
  blocks, local conditioning/dual compact-budget data, and nonpositive
  row-max/diagonal defect, these assumptions still leave the scalar comparison
  defect positive at stage one.  Red dependency status change: the final
  surface cannot derive `storedQRStageRowMaxComparisonDefectBudget <= 0`;
  that scalar comparison invariant remains the red bottleneck.

  LS.2g-in final-surface source-denominator rational-gamma
  scalar-comparison route elimination:
  `LSQRSolve.lean` now proves
  `storedDiagDominantComparisonCounterexample_finalSurface_sourceDenURationalGammaCanonicalSmallness`
  and
  `not_forall_diagDominant_activeMaxPivot_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_init_sourceDenURationalGammaCanonical_globalCompactBudget_rowMaxDiagDefect_signedAlphaDef_stored_trailing_sequence_actualU_sourceDen_nonneg_monoStageBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
  The same exact/zero-RHS final-surface witness satisfies the canonical
  source-denominator rational-gamma finite-max scalar with `Ucap = 0`, since
  the rational-gamma and Householder-factor cap terms collapse to zero.
  Replacing the raw compact-product field by source-denominator cap smallness
  still leaves the stage-one comparison defect positive.  Red dependency
  status change: the route "derive the comparison scalar from the final
  active/prefix surface plus canonical source-denominator rational-gamma
  finite-max scalar smallness" is eliminated.  The scalar comparison invariant
  itself remains the red bottleneck.

  LS.2g-io horizon-clamped source-denominator scalar-comparison handoff:
  `LSQRSolve.lean` now proves
  `storedQRStageRowMaxComparisonDefectBudget_nonpos_of_horizonBudget` and
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSourceDenURationalGammaCanonicalBounds_stageRowMaxComparisonDefect_offdiag_rows_of_horizonBudget`.
  The first lemma transfers the scalar comparison defect to
  `qrStageHorizonBudget n stageBudget`; the local source-control theorem then
  derives global budget monotonicity from the signed-stage compact recurrence
  and reuses the source-denominator/cap handoff.  `LeastSquaresSketch.lean`
  lifts this to the explicit-cap, actual-unit, and stored-lower sampled
  horizon siblings
  `...activePrefix_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_horizonBudget`,
  `...solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget`, and
  `...activePrefix_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget`.
  Full validation is clean for this horizon source-denominator handoff:
  focused builds, executable lookup, standard-only axiom audit, theorem-PDF
  compiles and rendered inspection, whitespace check, marker scan, and broad
  `lake build` all passed.
  Red dependency status change: the source-denominator probability route no
  longer exposes samplewise global stage-budget monotonicity.  The scalar
  comparison defect, diagonal dominance, active-pivot policy, signed-stage
  recurrence, source-denominator cap smallness, and the final generic
  QR/preconditioner theorem remain visible.

  Scalar-comparison active-pivot row-max theorem surface:
  `LSQRSolve.lean` now proves the source-control and solver wrappers with
  suffix
  `..._rowMaxDiagDefect_stageRowMaxComparisonDefect_offdiag_rows`, together
  with their actual-unit-roundoff siblings, and `LeastSquaresSketch.lean` now
  proves the probability wrappers
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_rowMaxDiagDefect_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver`
  and
  `..._stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid`.
  The explicit-validity horizon probability sibling
  `..._stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_horizonBudget`
  derives the displayed comparison from the scalar comparison defect, then
  calls the LS.2g-ib horizon row-max theorem, so the two-scalar probability
  surface keeps sampled `gammaValid` fields visible but no longer exposes
  samplewise global budget monotonicity.
  The latest horizon actual-unit probability sibling
  `..._stageRowMaxComparisonDefect_kappaInf_dualBudget_solver_of_actualUnitRoundoff_no_gammaValid_of_horizonBudget`
  derives sampled validity from `(s : ℝ) * fp.u < 1` and calls that
  explicit-validity horizon sibling, so the two-scalar actual-unit probability
  surface exposes neither sampled validity fields nor samplewise global budget
  monotonicity.  Full validation is clean for these horizon siblings: focused
  RandNLA least-squares build, executable lookup, standard-only axiom audit,
  theorem-PDF compiles, whole-PDF text extraction, rendered inspection of the
  scalar-comparison and not-proved pages, broad `lake build`,
  whitespace check, marker scan, and temporary-file cleanup all passed.
  These theorems replace the displayed samplewise or local
  `stageBudget <= rowMax` comparison family by the scalar finite condition
  `storedQRStageRowMaxComparisonDefectBudget <= 0`.  This closes only the
  comparison-interface dependency; the scalar row-max defect, scalar
  comparison defect, determinant/nonbreakdown or conditioning fields, dual
  compact-budget data, global compact-product smallness, and the final generic
  QR/preconditioner theorem remain open or visible.

  Scalar-comparison route elimination:
  `LSQRSolve.lean` now proves
  `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`
  and
  `not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
  These theorems lift the active-pivot oversized-budget obstruction from the
  displayed comparison family to the scalar finite comparison defect itself.
  Product compact-smallness does not rescue the route.  The red bottleneck now
  needs either a stronger concrete loop invariant proving the scalar
  comparison defect, a different route to the stage-diagonal scalar condition,
  or a final theorem that keeps this scalar field visible.

  Row-max-granted scalar-comparison route elimination:
  `LSQRSolve.lean` now proves
  `activeMaxPivotRowMaxComparisonCounterexample_rowMaxDiagDefectBudget_nonpos`,
  `activeMaxPivotRowMaxComparisonCounterexample_stageRowMaxComparisonDefectBudget_pos`,
  `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_rowMaxDiagDefect_implies_stageRowMaxComparisonDefectBudget_nonpos`,
  and
  `not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_rowMaxDiagDefect_implies_stageRowMaxComparisonDefectBudget_nonpos`.
  This rules out a stronger shortcut: even after the row-max scalar defect is
  supplied as a hypothesis, the active-pivot active/off-diagonal budget surface
  still cannot imply the scalar comparison defect, and adding product
  compact-smallness does not change that conclusion.  The red bottleneck still
  needs a genuine proof of the comparison defect from a stronger concrete loop
  invariant or a final theorem surface that keeps it visible.

  Row-max-alone stage-diagonal route elimination:
  `LSQRSolve.lean` now proves
  `activeMaxPivotRowMaxComparisonCounterexample_stageDiagLowerDefectBudget_pos`
  and
  `not_forall_rowMaxDiagDefectBudget_implies_stageDiagLowerDefectBudget_nonpos`.
  This rules out another tempting shortcut in the row-max bridge: even if the
  row-max scalar defect is already nonpositive, a larger stage budget can make
  the scalar stage-diagonal defect positive.  The stage-diagonal route
  therefore still needs the comparison scalar, the pointwise
  stage-budget/row-max comparison, a stronger loop invariant, or an explicit
  visible domain hypothesis.

  Product/active row-max-granted stage-diagonal route elimination:
  `LSQRSolve.lean` now proves
  `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_rowMaxDiagDefect_implies_stageDiagLowerDefectBudget_nonpos`
  and
  `not_forall_leadingBlock_upper_det_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_rowMaxDiagDefect_implies_stageDiagLowerDefectBudget_nonpos`.
  The same witness satisfies active max-pivoting, active/off-diagonal budget
  control, compact-product smallness with `B = 1/16`, and the nonpositive
  row-max scalar defect, but with stage budget `4` the scalar
  stage-diagonal defect is positive.  Thus the active/product surface still
  cannot replace the comparison scalar or a stronger concrete invariant.

  Diagonal-dominant scalar-comparison active-pivot surface:
  `LSQRSolve.lean` now proves
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_stageRowMaxComparisonDefect_offdiag_rows`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_stageRowMaxComparisonDefect_offdiag_rows`.
  This closes a listed theorem-surface dependency on separate determinant and
  row-max-defect fields for the local active-pivot branch: diagonal dominance
  supplies leading-block determinant nonzeroness, and diagonal dominance plus
  the scalar comparison defect supplies the scalar stage-diagonal condition.
  The red bottleneck is now sharper: a concrete pivoted/sorted/off-diagonal
  loop must prove local diagonal dominance or an equivalent off-diagonal
  invariant, prove the scalar comparison defect, prove the conditioning/dual
  and compact-product fields, or keep those assumptions visible in the final
  QR/preconditioner theorem.

  Probability-level diagonal-dominant scalar-comparison surface:
  `LeastSquaresSketch.lean` now proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver`.
  This lifts the LS.2g-hd local dependency reduction to the sampled equation
  (8) theorem: samplewise local diagonal dominance supplies the determinant and
  row-max scalar-defect fields, and the scalar comparison defect supplies the
  displayed stage-budget/row-max comparison through the existing finite
  package.  The remaining red dependencies are unchanged but clearer:
  diagonal dominance or equivalent off-diagonal control, the scalar comparison
  defect, conditioning/dual compact-budget data, active-pivot policy,
  compact-product smallness, and the final concrete QR/preconditioner theorem.

  Diagonal-dominance/comparison-defect route elimination:
  `LSQRSolve.lean` now proves
  `activeMaxPivotRowMaxComparisonCounterexample_diagDominant` and
  `not_forall_diagDominant_implies_stageRowMaxComparisonDefectBudget_nonpos`.
  The row-max-granted scalar-comparison witness is locally diagonally dominant,
  but the uniform stage budget `3` still exceeds the displayed strict-upper
  row maximum `2`, making the scalar comparison defect positive.  This rules
  out using local diagonal dominance alone to discharge
  `storedQRStageRowMaxComparisonDefectBudget <= 0`.  The scalar comparison
  defect must come from a genuinely stronger pivoted/sorted/off-diagonal loop
  invariant or remain visible.

  Diagonal-dominance/product-smallness comparison route elimination:
  `LSQRSolve.lean` now proves
  `activeMaxPivotRowMaxComparisonCounterexample_productBudget` and
  `not_forall_diagDominant_product_budget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
  The same locally diagonally dominant witness satisfies the displayed
  product-smallness inequality for `B = 1 / 16`, but the scalar comparison
  defect remains positive.  This rules out using compact-product smallness as
  a hidden proof of the comparison scalar once diagonal dominance is available.

  Active-surface comparison route elimination:
  `LSQRSolve.lean` now proves
  `not_forall_diagDominant_product_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_stageRowMaxComparisonDefectBudget_nonpos`.
  This strengthens the preceding failed route by also granting the active
  finite-max branch's current active data: positive active-block mass, active
  max-pivoting, nonnegative stage budgets, active-block entry budget control,
  and displayed off-diagonal budget control.  The same witness still has
  positive scalar comparison defect.  Red dependency status change: the route
  "prove the comparison scalar from diagonal dominance plus product smallness
  plus the current active/off-diagonal budget surface" is eliminated.  The
  comparison scalar remains a required concrete loop invariant or visible
  source/domain field.

  Finite-max compact-product handoff for the active diagonal-dominant
  scalar-comparison branch:
  `LSQRSolve.lean` now proves
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSmallness_stageRowMaxComparisonDefect_offdiag_rows`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSmallness_stageRowMaxComparisonDefect_offdiag_rows`;
  `LeastSquaresSketch.lean` now proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSmallness_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_kappaInf_dualBudget_solver`.
  These wrappers consume the existing canonical finite-max smallness theorem to
  derive the raw compact-product field internally, then reuse the global-product
  diagonal-dominant scalar-comparison source-control, solver, and equation (8)
  wrappers.  The compact-product dependency is therefore reduced to the
  visible finite-max scalar for this branch, while diagonal dominance, the
  comparison scalar, conditioning/dual data, active-pivot policy, and the final
  concrete QR/preconditioner theorem remain open.

  Concrete-dual finite-max handoff for the active diagonal-dominant
  scalar-comparison branch:
  `LSQRSolve.lean` now proves
  `storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_diagDominant_concreteDualProductSequenceBudget`,
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSmallness_stageRowMaxComparisonDefect_concreteDual_offdiag_rows`,
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSmallness_stageRowMaxComparisonDefect_concreteDual_offdiag_rows`;
  `LeastSquaresSketch.lean` now proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSmallness_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_concreteDual_solver`.
  This removes the visible `κ`, `K`, and dual compact-budget fields from the
  active finite-max scalar-comparison branch by deriving norm-square
  nonbreakdown from diagonal dominance plus the per-pivot product-sequence
  budget.  Red dependency status changes: conditioning/dual compact-budget data
  is closed for this branch as a visible theorem-surface dependency.  The
  remaining red dependencies are local diagonal dominance or equivalent
  off-diagonal control, the scalar comparison defect, active-pivot policy,
  signed-stage recurrence budgets, the finite-max scalar inequality, and the
  final concrete QR/preconditioner theorem.

  Actual-unit validity closure for the active concrete-dual finite-max branch:
  `LSQRSolve.lean` now proves
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSmallness_stageRowMaxComparisonDefect_concreteDual_offdiag_rows_of_actualUnitRoundoff_no_gammaValid`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_finiteMaxSmallness_stageRowMaxComparisonDefect_concreteDual_offdiag_rows_of_actualUnitRoundoff_no_gammaValid`;
  `LeastSquaresSketch.lean` now proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_finiteMaxSmallness_activeMaxPivot_diagDominant_stageRowMaxComparisonDefect_concreteDual_solver_of_actualUnitRoundoff_no_gammaValid`.
  These wrappers derive the explicit `gammaValid` guards from
  `(m : Real) * fp.u < 1` or `(s : Real) * fp.u < 1`, so the active
  concrete-dual finite-max branch no longer exposes abstract validity fields.
  Red dependency status change: the actual-unit validity-surface dependency is
  closed for this branch.  The remaining red fields are unchanged: local
  diagonal dominance or equivalent off-diagonal control, the scalar comparison
  defect, active-pivot policy, signed-stage recurrence budgets, the finite-max
  scalar inequality, and the final concrete QR/preconditioner theorem.
