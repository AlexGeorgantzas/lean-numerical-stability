# Higham Chapter 21 Formalization Report

## Source And Scope

- Edition: Nicholas J. Higham, 2nd ed., SIAM, 2002
- Chapter: 21, “Underdetermined Systems”
- Printed pages: 407–414
- Source file: `References/1.9780898718027.ch21.pdf`
- Mode: core
- Parallel split: 4
- Planning documents: blueprint, Split 4 contract, chapter index
- Selected-scope gate: **PASS** under the strict source-strength audit

The source inventory contains 27 rows: 21 selected mathematical or
algorithmic rows and six intentional exclusions. All 21 selected rows pass.
Theorem 21.4 now has source-facing Householder and retained-trace Givens
endpoints whose computed nonbreakdown and replay-smallness facts are derived
from full row rank, gamma validity, and the printed-form smallness condition.

## Completed Selected Targets

| Source group | Main Lean declarations/modules | Theorem surface |
|---|---|---|
| Equations (21.1)–(21.5) | `UnderdeterminedSpec.lean`, `UnderdeterminedSolve.lean`, `Higham21QRFoundations.lean` | Exact block QR, minimum-norm, pseudoinverse, and SNE Gram algebra |
| Theorem 21.1 and (21.6)–(21.9) | `Higham21Perturbation*.lean`, `Higham21Eq21_8.lean`, `Higham21Eq21_9.lean` | Exact first-order terms, rank stability, fixed-radius finite remainders, and genuine `O(t²)` forms |
| Projector and scaling prose | `Higham21ProjectorNorm.lean`, `Higham21Condition.lean` | Exact complement-projector norm and row-scaling invariance |
| Lemma 21.2 | `UnderdeterminedSolve.lean` | Single perturbation, minimum-norm recovery, and printed square-sum bounds |
| Theorem 21.3 | `UnderdeterminedSolve.lean`, `Higham21Theorem21_3Attainment.lean` | Correct infimum formula, lower/upper constructions, exact/closure attainment, and nonattainment witness |
| Equation (21.10) and Householder Theorem 21.4 | `UnderdeterminedSolve.lean`, Chapter 19 QR interfaces, `Higham21Theorem214SourceClosure.lean` | Actual rounded panel/solve/action endpoint; `Higham21QMethodFullRowRankComputedQRDomain.of_source_smallness` derives computed top-block nonbreakdown by QR perturbation and full-rank stability |
| Givens Theorem 21.4 | `Higham21Givens.lean`, `Higham21GivensRounded.lean`, `Higham21GivensClosure.lean`, `Higham21Theorem214SourceClosure.lean` | Actual retained-trace endpoint; source producers derive computed diagonal nonbreakdown and bound the complete replay recurrence below one from one operational gamma-validity index |
| Q method equation (21.11) | `Higham21Equation21_11.lean`, `Higham21Eq21_11Uniform.lean`, `Higham21Equation21_11Scalar.lean` | Relative forward bound, fixed-radius refinement, and the remaining square scalar boundary |
| SNE equation (21.11) | `Higham21SNEForward.lean`, `Higham21SNEActualOutput.lean`, `Higham21SNESigned.lean`, `Higham21SNEConditionTransfer.lean`, `Higham21SNEQRMajorant.lean`, `Higham21SNERemainderBounds.lean`, `Higham21SNEClosure.lean`, `Higham21SNEUniform.lean` | Actual Householder panel, two rounded triangular solves, rounded `Aᵀŷ` formation, relative `xhat` versus canonical `x`, original `cond2(A)` first-order term, fixed-radius uniform quadratic coefficient, and explicit `fp.u²` remainder |
| Corrected MGS recurrence | `Higham21MGS.lean`, `Higham21MGSRounded.lean` | Exact repair algebra and rounded local operations |

The exact row-to-declaration map is in `CHAPTER21_SOURCE_INVENTORY.md`.

## Reused From Repository Or Mathlib

| Source concept/result | Existing declaration/module |
|---|---|
| Abstract floating-point operations and gamma calculus | `FPModel`, `Rounding.lean`, rounded matrix-vector and triangular-solve operations |
| Householder QR and Q application | Chapter 19 QR modules, including panel backward error and rounded action |
| Finite matrix algebra and norms | `MatrixAlgebra.lean`, `Norms.lean`, Mathlib finite matrices and asymptotics |
| Cholesky/normal-equation intermediates | existing Cholesky solve and backward-error declarations |

## New Dependencies

| Declaration/module | Why needed | Used by | Status |
|---|---|---|---|
| `Higham21PerturbationRadius.lean` | Uniform inverse/remainder radius | Theorem 21.1 and (21.6) | COMPLETE |
| `Higham21ProjectorNorm.lean` | Exact `min{1,n-m}` projector norm | (21.8), (21.9) | COMPLETE |
| `Higham21Eq21_11Uniform.lean` | Uniform Q-method remainder | Q side of (21.11) | COMPLETE FOR ITS RECORDED DOMAIN |
| `Higham21Equation21_11Scalar.lean` | Close the square scalar boundary | Q side of (21.11) | COMPLETE |
| `Higham21GivensClosure.lean` | Connect staged rotations to the actual rounded replay | Givens side of Theorem 21.4 | COMPLETE |
| `Higham21Theorem214SourceClosure.lean` | Derive Householder/Givens top-block nonbreakdown and actual Givens replay smallness | Both branches of Theorem 21.4 | COMPLETE |
| `Higham21SNESigned.lean` | Preserve factorwise QR cancellation | SNE side of (21.11) | COMPLETE |
| `Higham21SNEConditionTransfer.lean` | Fixed-radius pseudoinverse, condition, and solution transfer | SNE side of (21.11) | COMPLETE |
| `Higham21SNEQRMajorant.lean` | Componentwise QR-action/source majorants | SNE side of (21.11) | COMPLETE |
| `Higham21SNERemainderBounds.lean` | Factor-difference, signed-remainder, QR-action, and formation estimates | SNE side of (21.11) | COMPLETE |
| `Higham21SNEClosure.lean` | Instantiate the actual Householder SNE algorithm and assemble the relative endpoint | SNE side of (21.11) | COMPLETE |
| `Higham21SNEUniform.lean` | Freeze all active QR, solve, and remainder quantities on a source-defined master radius and convert `theta²` to `fp.u²` | SNE side of (21.11) | COMPLETE |

## External Proof Sources

| Selected claim | Source and exact location | Role | Local Lean closure | Status |
|---|---|---|---|---|
| SNE side of (21.11) | Demmel–Higham 1993, §3, equations (3.10)–(3.20) | Signed factorwise derivation, especially (3.18) and (3.20) | `Higham21SNESigned.lean` plus `higham21_sne_householder_actual_output_source_relative_q_uniform` and `higham21_sne_householder_actual_output_source_relative_unit_roundoff_sq` in `Higham21SNEUniform.lean` | ADOPTED AND FORMALIZED |
| Lemma 21.2 | Kielbasiński–Schwetlick result cited on p. 410 | One-perturbation construction | `higham21_lemma21_2_source_bundle` | FORMALIZED |
| Theorem 21.3 | Sun–Sun result cited on p. 411 | Formula and attainment analysis | local formula/attainment modules | FORMALIZED WITH BOUNDARY CORRECTION |

The detailed trust record is in `CHAPTER21_PROOF_SOURCE_LEDGER.md`.

## Skipped Items

| Source location | Summary | Reason code |
|---|---|---|
| p. 412 | Negative SNE backward/residual warning | SKIP-QUALITATIVE |
| p. 413 | Corrected-MGS “essentially” stable sentence | SKIP-QUALITATIVE |
| p. 414 | LAPACK routine descriptions | SKIP-EDITORIAL |
| p. 414 | Problem 21.1 and (21.12)–(21.14) | OPTIONAL-PROBLEM-NOT-SELECTED |

## Empirical Source Outputs

| Source location | Printed claim/output | Missing machine details | Precise replacement | Status |
|---|---|---|---|---|
| p. 413, Table 21.1 | `cond₂(A)=7.6e12`, orthogonality `9e-3`, and four backward-error values | exact program, arithmetic path, platform, library/compiler, and decimal I/O | symbolic Q/SNE/MGS algorithms and stability theorems | SKIP-EMPIRICAL |

## Selected-row closure

- No selected row is open. For Theorem 21.4,
  `Higham21QMethodFullRowRankComputedQRDomain.of_source_smallness` derives the
  Householder computed-QR nonbreakdown predicate;
  `higham21_givens_actual_topBlock_nonbreakdown_of_source_smallness` and
  `Higham21GivensActualReplayEtaQ_lt_one_of_operational_gammaValid` derive the
  Givens `hdiag` and `hQsmall` premises. The two source-facing rowwise endpoints
  consume these derived guards.

## Deferred And Benchmark Items

- No selected mathematical row is intentionally deferred.
- The Section 21.3 method comparison is a future
  `BENCHMARK-COMPARISON`; the historical decimals are not benchmark truth.

## Hidden-Hypothesis Summary

- For the final SNE relative endpoint, `hm`, `hn`, `hdet`, and `hb` are
  source/domain assumptions: the dimension regime, full row rank through Gram
  nonsingularity, and a nonzero right-hand side for relative normalization.
- `hvalidQR` and `hmGamma` are `gammaValid` floating-point validity premises;
  `hdiag` is computed triangular nonbreakdown; and `hrho_pos` asserts
  positivity of the Householder perturbation scale. None is an assumed error
  conclusion.
- The fixed-radius theorem assumes `gamma_m + rho ≤ tau < 1`,
  `higham21Eq21_11UniformGramContraction A tau < 1`, and
  `tau * higham21SNEQUniformSolveMultiplier A tau ≤ 1/2`. The explicit
  `fp.u²` theorem additionally assumes `(m : ℝ) * fp.u ≤ 1/2` and
  `(m * householderConstructApplyGammaIndex (m+k) : ℝ) * fp.u ≤ 1/2`.
- `higham21SNEQUniformUnitRoundoffSecondOrderCoefficient A b tau` depends only
  on the source data, dimensions, and chosen radius. The final result is an
  explicit pointwise `fp.u²` remainder theorem; it does not need active QR
  directions, nearby factors, or the rounded normal solution as coefficient
  inputs.
- Rejected suspicious artifacts: target-shaped SNE transfer premises,
  supplied Givens replay certificates, and fixed-precision tautological
  quadratic constants.
- Theorem 21.4's computed triangular nonbreakdown and Givens replay-smallness
  facts are now internal conclusions. Only explicit operation-count
  `gammaValid` premises remain on the source-facing rounded endpoints.

## Weak-Component And Bottleneck Summary

| Component | First check | Independent check | Status |
|---|---|---|---|
| Theorem 21.1 and equations (21.6)–(21.9) | Focused builds/type review | source constants, rank, and remainder audit | PASS |
| Lemma 21.2 | source-bundle review | assumption/axiom audit | PASS |
| Theorem 21.3 | formula and attainment builds | boundary/source correction audit | PASS |
| Householder Theorem 21.4 | actual rounded path review | source wrapper derives embedded `lsTheorem20_4ComputedQRNonbreakdown` by QR perturbation and rank stability | PASS |
| Givens Theorem 21.4 | stored replay review | source wrapper derives `hdiag` and `hQsmall` from source smallness and the operational schedule index | PASS |
| Q method (21.11) | main/uniform theorem review | scalar boundary and standard-axiom audit | PASS |
| SNE (21.11) | fixed-radius and explicit `fp.u²` source-facing theorems focused compile | actual-object, original-condition first-order term, source-defined quadratic coefficient, and public smallness-assumption audit | PASS |

## Verification

The focused Chapter 21 verification results are:

```text
lake env lean NumStability/Algorithms/Underdetermined/Higham21SNEUniform.lean  PASS
higham21_sne_householder_actual_output_source_relative_q_uniform                  COMPILED
higham21_sne_householder_actual_output_source_relative_unit_roundoff_sq           COMPILED
lake build NumStability.Algorithms.Underdetermined.Higham21Theorem214SourceClosure
                                                                                  PASS (3,084 jobs)
lake build NumStability.Algorithms.Underdetermined.Higham21                  PASS (3,108 jobs)
lake build NumStability.Algorithms                                           PASS (3,848 jobs)
lake build                                                                         PASS (3,901 jobs)
#print axioms higham21_sne_householder_actual_output_source_relative_unit_roundoff_sq
  [propext, Classical.choice, Quot.sound]
```

The warnings replayed by the aggregate builds are inherited from pre-existing
modules; the new Chapter 21 modules compile without warnings.

## Documentation

- Inventory: `docs/chapter21/CHAPTER21_SOURCE_INVENTORY.md`
- Not-proved ledger: `docs/chapter21/CHAPTER21_NOT_PROVED_LEDGER.md`
- Proof-source ledger: `docs/chapter21/CHAPTER21_PROOF_SOURCE_LEDGER.md`
- Existing detailed coverage ledger: `docs/source_coverage/higham_ch21.md`

## Selected-Scope Disposition

All 21 selected rows, including both branches of Theorem 21.4, are closed at
source strength. The six intentional exclusions remain classified in the
inventory and not-proved ledger; they are not proof gaps.
