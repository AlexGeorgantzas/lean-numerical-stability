# Chapter 1 Proof-Source Ledger

This ledger records proof-source acquisition for open paper-level claims in
`references/Chapter01_full.pdf`.  It complements
[`CHAPTER01_FULL_FORMALIZATION_LEDGER.md`](CHAPTER01_FULL_FORMALIZATION_LEDGER.md)
and bottleneck ledgers such as
[`CHAPTER01_BENEFICIAL_POWER_METHOD_BOTTLENECK.md`](CHAPTER01_BENEFICIAL_POWER_METHOD_BOTTLENECK.md).

## Closure Rule

External sources are proof guides, not hypotheses.  A source row closes only
when the cited statement has been formalized locally or replaced by a locally
proved theorem with all assumptions exposed in Lean.  No Chapter 1 paper-level
claim is closed merely by citing a theorem number, book page, or external
paper.

## Proof Completeness Classification

| Source target | Chapter 1 proof status | Primary missing step | Proof-source status |
|---|---|---|---|
| §1.15 beneficial-rounding power-method observation | Explanation plus appeal to perturbation theory/MATLAB behavior, not a complete proof | Concrete dominant-eigenpair/eigencomponent certificate for the stored matrix `A + DeltaA`, MATLAB/BLAS first-step operation order, and the 38-iteration display certificate | Active proof-source chain C1.15-BPM below |
| §1.15 inverse-iteration beneficial-rounding observation | Explanation plus citation-level perturbation-theory appeal | Perturbation theorem or concrete rounded shifted-solve trace proving the solve error is nearly parallel to the target eigenvector | Open; shares spectral perturbation sources with C1.15-BPM, but also needs a shifted-solve FP trace |

## Active Proof-Source Chain: C1.15-BPM Beneficial Power Method

### Paper Claim

In §1.15, Higham states that MATLAB's first power-method step for the displayed
matrix produces entries of order `10^-16`, and after 38 iterations gives a good
dominant eigenpair approximation.  The explanation is that the stored matrix is
`A + DeltaA`; its dominant eigenpair is close to that of `A`; and the displayed
start vector has a tiny nonzero component in the dominant eigendirection of
`A + DeltaA`, which is then amplified by the power method.

### Local Closed Layer

- Exact displayed matrix eigenvalue line and zero-eigenvector step:
  `beneficialPowerCharDet_eq`, `beneficialPowerCharDet_root_zero`,
  `beneficialPowerCharDet_root_small`,
  `beneficialPowerCharDet_root_dominant`,
  `beneficialPowerStart_isRightEigenpair_zero`,
  `beneficialPowerFirstStep_zero`.
- Entrywise IEEE-double storage first-step vector:
  `beneficialPowerMatrixIeeeDoubleRounded_firstStep_eq` and
  `beneficialPowerMatrixIeeeDoubleRounded_firstStep_abs_between_one_e17_one_e16`.
- Operation-order split:
  `beneficialPowerMatrixIeeeDoubleRoundedFirstStepLeftToRight_ne_firstStep`
  and
  `beneficialPowerMatrixIeeeDoubleRoundedFirstStepRightToLeft_eq_firstStep`.
- Non-enumerative power-method theory bridge:
  `powerMethodIterate_dominant_plus_finite_tail`,
  `powerMethod_finite_tail_vecNorm2_ratio_tendsto_zero_of_geometric_bound`,
  `powerMethodIterate_dominant_scaled_residual_tendsto_zero_of_finite_tail`,
  `PowerMethodDominantFiniteTailCertificate.scaled_residual_tendsto_zero`,
  and the concrete handoff theorem
  `beneficialPowerStoredStart_dominant_component_certificate_scaled_residual_tendsto_zero`.

### Source Chain

| Step | Source | Exact location | Needed Lean target | Local status |
|---|---|---|---|---|
| C1.15-BPM-S1 | Higham, `references/Chapter01_full.pdf` | §1.15, PDF text lines around extracted lines 1191--1216 | Paper-level target: `beneficialPowerStoredPowerMethod_scaled_residual_tendsto_zero` plus optional `beneficialPowerMatlabThirtyEight_display_certificate` | Source claim extracted; exact matrix algebra, first-step storage layer, operation-order caveat/certificate, finite-tail convergence bridge, and the concrete certificate-to-convergence handoff are closed locally. Concrete stored-matrix eigencomponent certificate and MATLAB trace remain open |
| C1.15-BPM-S2 | Greenbaum, Li, and Overton, "First-order Perturbation Theory for Eigenvalues and Eigenvectors", arXiv:1903.00785, <https://arxiv.org/abs/1903.00785> | §2 Assumption 1 and Theorem 1: analytic perturbation of a simple eigenvalue; §3 Lemma 1 and Theorem 2: right/left eigenvector perturbation and reduced-resolvent derivative formula | Reusable simple-eigenvalue perturbation theorem for a finite matrix path `A(t)=A+tE`, exposing existence/continuity of a nearby simple eigenpair and a first-order eigencomponent/eigenprojector certificate | Advisory source acquired; not formalized locally. Its assumptions use complex matrices, left/right eigenvectors, analytic perturbation, and reduced resolvent data, so Lean route likely needs either complex-matrix infrastructure or a real-specialized wrapper |
| C1.15-BPM-S3 | Same Greenbaum--Li--Overton source | Introduction and §2--§3 references to Kato, Wilkinson, Stewart--Sun, Lancaster, and Lidskii; §3 Lemma 1 identifies the block decomposition and reduced resolvent | Source-chain comparison for older perturbation-theory route if the modern theorem's analytic setup is too heavy | Advisory only; older theorem bodies not acquired. Use only for route selection unless primary texts are inspected directly |
| C1.15-BPM-S4 | Bauer--Fike eigenvalue inclusion theorem, original source Bauer and Fike, "Norms and Exclusion Theorems", Numerische Mathematik 2, 137--141, 1960 | Eigenvalue inclusion for diagonalizable matrices under perturbation | Possible gap-preservation lemma locating perturbed eigenvalues near the exact eigenvalues and preserving a unique dominant eigenvalue under a sufficiently small perturbation | Candidate route only. It can help with eigenvalue location/gap preservation, but it does not by itself supply the dominant eigenvector component of the stored start vector |
| C1.15-BPM-S5 | Local exact computation route | `beneficialPowerMatrixIeeeDoubleRounded` in `BeneficialRounding.lean` | Instead of a general perturbation theorem, prove exact/interval spectral facts for the concrete entrywise IEEE-double rounded `3 x 3` matrix: dominant eigenvalue interval, finite eigenbasis, nonzero start-vector component, and tail spectral-ratio bound | Open route choice. Potentially source-faithful and finite-dimensional, but may require substantial real-root/eigenvector interval infrastructure |

### Chosen Next Route

The next proof attempt should not enumerate iterations or operation cases.
The reusable certificate-to-convergence theorem has been implemented.  The next
dependency is to construct the concrete certificate itself, using either a
locally proved simple-eigenvalue perturbation theorem or a concrete stored-matrix
spectral interval certificate to produce the fields consumed by
`PowerMethodDominantFiniteTailCertificate.scaled_residual_tendsto_zero`.

Target shape:

```lean
-- certificate construction target, not yet implemented
theorem beneficialPowerStoredStart_dominant_component_certificate :
  -- hypotheses expose the stored matrix, dominant right eigenvector, finite
  -- tail eigenvectors, nonzero dominant coefficient, and q < 1 spectral gap
  BeneficialPowerStoredStartDominantComponentCertificate m
```

This target is a dependency handoff, not a final paper-level closure.  The
paper-level §1.15 row remains open until this stored-matrix certificate and, if
the exact MATLAB observation is required, the MATLAB operation-order and
38-iteration display certificates are proved locally.
