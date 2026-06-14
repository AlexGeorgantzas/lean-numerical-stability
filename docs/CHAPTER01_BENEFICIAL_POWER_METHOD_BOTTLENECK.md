# Chapter 1 Beneficial Power-Method Bottleneck

Status: OPEN

Source scope: `references/Chapter01_full.pdf`, §1.15, line-by-line ledger row
`1085--1133`.

Proof-source ledger:
[`CHAPTER01_PROOF_SOURCE_LEDGER.md`](CHAPTER01_PROOF_SOURCE_LEDGER.md),
active chain `C1.15-BPM`.

## Source Claim

The source's beneficial-rounding power-method example says that the displayed
matrix is not stored exactly, so the computer works with `A + DeltaA`; the
displayed start vector then has a tiny component in the eigendirection
corresponding to the largest-modulus eigenvalue of `A + DeltaA`, and the power
method amplifies that component enough to obtain the reported dominant
eigenpair after 38 iterations.

## Bottleneck Theorem Family

The remaining paper-level closure is not another finite-component convergence
proof.  It requires a concrete stored-matrix/eigenspace certificate:

1. `beneficialPowerStoredMatrix_has_simple_dominant_eigenpair`
2. `beneficialPowerStoredStart_dominant_component_nonzero`
3. `beneficialPowerStoredPowerMethod_scaled_residual_tendsto_zero`
4. `beneficialPowerMatlabFirstStep_trace_matches_operation_order`
5. `beneficialPowerMatlabThirtyEight_display_certificate`

Names are targets, not existing Lean declarations.

## Closed Dependencies

- Exact displayed eigenvalue/eigenvector algebra for `beneficialPowerMatrix`.
- Exact zero first step for the displayed matrix/start vector.
- Entrywise IEEE-double storage obstruction for the displayed matrix.
- Concrete entrywise IEEE-double first-step vector
  `[2^-54, -2^-54, -2^-55]^T`.
- Left-to-right rounded-add caveat: that operation order gives third component
  `0` and is not the entrywise row-sum vector.
- Right-to-left rounded-add certificate: that operation order recovers the
  entrywise first-step vector.
- Finite-tail power-method theory bridge:
  `powerMethodIterate_dominant_plus_finite_tail`,
  `powerMethod_finite_tail_vecNorm2_ratio_tendsto_zero_of_geometric_bound`,
- Certificate-to-convergence handoff:
  `PowerMethodDominantFiniteTailCertificate.scaled_residual_tendsto_zero`
  and
  `beneficialPowerStoredStart_dominant_component_certificate_scaled_residual_tendsto_zero`.

## Open Dependencies

- A locally proved perturbation theorem for a simple dominant eigenvalue and
  eigenvector/eigenprojection of `A + DeltaA`, with hypotheses strong enough to
  prove a dominant spectral gap for the stored matrix in this example.
- A concrete certificate that the stored start vector has nonzero component in
  that dominant eigendirection.
- A concrete source or explicitly assumed MATLAB/BLAS operation-order
  convention for the first matrix-vector product.  The right-to-left trace is
  reachable, but the left-to-right trace proves operation order matters.
- A normalization and display certificate for the reported 38-iteration
  observation, if the exact printout is required rather than the qualitative
  convergence explanation.

## Route Status

- Rejected route: prove thousands of operation or iteration cases one by one.
  The finite-tail bridge and operation-order certificates are non-enumerative.
- Rejected route: identify the entrywise row-sum theorem with MATLAB's first
  step without a primitive-operation convention.  The left-to-right caveat
  shows this is unsound.
- Open route choice: either prove exact spectral facts for the concrete
  entrywise IEEE-double rounded matrix, or prove a reusable simple-eigenvalue
  perturbation theorem and instantiate it for the stored perturbation.

## Proof-Source Candidates

The authoritative proof-source route is now maintained in
[`CHAPTER01_PROOF_SOURCE_LEDGER.md`](CHAPTER01_PROOF_SOURCE_LEDGER.md).
Summary:

- Anne Greenbaum, Ren-Cang Li, and Michael L. Overton,
  "First-order Perturbation Theory for Eigenvalues and Eigenvectors",
  arXiv:1903.00785.  Advisory only, not formalized.  Relevant locations:
  §2 Assumption 1 and Theorem 1 for analytic perturbation of a simple
  eigenvalue; §3 Lemma 1 and Theorem 2 for the corresponding right/left
  eigenvector perturbation and reduced-resolvent formula.  The paper also
  identifies older source routes through Kato, Wilkinson, Stewart--Sun,
  Lancaster, and Lidskii.
- Bauer--Fike-style eigenvalue inclusion remains a candidate for locating
  perturbed eigenvalues and preserving the dominant gap, but by itself it does
  not supply the eigenvector/dominant-component certificate needed for the
  source's power-method explanation.

## Next Lean Target

Before any more §1.15 surrounding adapters, formalize the smallest local theorem
that can construct the concrete stored-matrix certificate consumed by the closed
handoff theorem:

```lean
-- certificate construction target, not yet implemented
theorem beneficialPowerStoredStart_dominant_component_certificate :
  -- hypotheses expose the chosen stored matrix and perturbation radius
  -- conclusion supplies a dominant eigencomponent decomposition of the
  -- displayed start vector with nonzero dominant coefficient and a finite
  -- tail spectral-ratio bound q < 1
  BeneficialPowerStoredStartDominantComponentCertificate m
```

The existing finite-tail theorem should be the downstream consumer of this
certificate, not a reason to reopen component-by-component convergence proofs.
