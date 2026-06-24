# Higham Chapter 11 Formalization Report

## Source And Scope

- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002.
- Chapter: 11, "Symmetric Indefinite and Skew-Symmetric Systems", printed pp. 213-229.
- Source files: `References/1.9780898718027.ch11.pdf`; Appendix A source `References/1.9780898718027.appa.pdf`.
- Mode: proof-completion pass in core needs-based mode.
- Parallel split: Split 2. Previous split allowed for imports: Split 1 only.
- Planning documents consulted: `chapter_splitting/HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md`, Split 2 section of `chapter_splitting/split_primary_contracts.md`, and Chapter 11 rows of `chapter_splitting/chapter_index.md`.
- Chapter fully formalized: no. All selected non-closed rows below are classified as `WAIT-PREVIOUS-SPLIT`, `DEFER-LATER-CHAPTER`, or `SKIP`.

## Proof-Completion Update

This pass closed local Appendix/source algebra that did not require the missing floating-point stability stack:

| Source item | Lean declaration(s) | File | Status |
|---|---|---|---|
| Problem 11.1 pivot existence lemma | `higham11_problem_11_1_principalTwoByTwoDet`, `higham11_problem_11_1_zero_of_symmetric_singular_principal_pivots` | `LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` | newly proved |
| Problem 11.2 overflow-safe 2 by 2 inverse formula | `higham11_problem_11_2_twoByTwoPivot`, `higham11_problem_11_2_twoByTwoPivotScaledInverse`, `higham11_problem_11_2_twoByTwoPivot_scaledInverse_spec` | same | newly proved |
| Problem 11.2 determinant-negativity algebra | `higham11_problem_11_2_det_negative_of_pivot_bound` | same | newly proved |
| Problem 11.4 SPD obstruction to indefinite 2 by 2 pivots | `higham11_problem_11_4_spd_no_negative_twoByTwo_principal_det` | same | newly proved, reuses Chapter 10 SPD minor theorem |
| Problem 11.7 modified-omega SPD second-test algebra | `higham11_problem_11_7_modifiedOmega_second_test_from_spd_minor` | same | newly proved |
| Problem 11.8 complete/rook exact factorization of the (11.6) example | `higham11_problem_11_8_rookCompleteExampleA`, `higham11_problem_11_8_rookCompleteExampleL`, `higham11_problem_11_8_rookCompleteExampleD`, `higham11_problem_11_8_rookCompleteExample_factorization` | same | newly proved |
| Problem 11.9(a) symmetric quasidefinite nonsingularity | `higham11_problem_11_9_quasidefinite_kernel_trivial` | same | newly proved kernel-trivial block-system proof |
| Problem 11.9(c) nonsymmetric positive definiteness reduction | `higham11_problem_11_9_signed_block_quadratic_pos`, `higham11_problem_11_9_nonsymPosDef_of_symPartSPD` | same | newly proved concrete signed-block quadratic proof plus wrapper around Chapter 10 result |

## Source Inventory And Classification

`Previous-split dependency` is stated for every non-closed row.

| ID | Source location | Kind | Statement summary | Classification | Previous-split dependency | Lean artifact/status |
|---|---|---|---|---|---|---|
| H11-intro-1 | p. 214 | definition/prose | Symmetric indefinite iff positive and negative eigenvalues exist | WAIT-PREVIOUS-SPLIT | Yes, direct: Split 1 `H06.svd`/spectral-eigenvalue family; do not redefine eigenvalue/inertia locally | not formalized |
| H11-intro-2 | p. 214 | equation | Block LDLT `PAP^T = LDL^T` | CLOSED | none | `higham11_1_BlockLDLTSpec` |
| (11.1) | p. 214 | numbered equation | Block LDLT factorization specification | CLOSED | none | `higham11_1_BlockLDLTSpec` |
| H11-inertia | p. 214 footnote | definition/prose | Inertia triple and Sylvester inertia theorem use | WAIT-PREVIOUS-SPLIT | Yes, direct: Split 1 spectral/eigenvalue/inertia foundations | `higham11_problem_11_2_inertiaFormula` records the formula only |
| H11-aasen-intro | p. 214 | equation/prose | Aasen `PAP^T = LTL^T` high-level factorization | CLOSED as source spec | none | `higham11_8_AasenSpec` |
| (11.2) | p. 214 | numbered equation | First pivot block partition with nonsingular `E` | CLOSED for invertible-pivot predicate | none | `higham11_2_NonsingularPivotBlock`; Problem 11.1 closes the nonzero-matrix pivot-existence algebra |
| (11.3) | p. 215 | numbered equation | Symmetric Schur complement `B - CE^{-1}C^T` | CLOSED | none | `higham11_3_symmetricSchurComplement` |
| Alg 11.1 | p. 215 | algorithm | Bunch-Parlett complete pivoting first-stage choice | CLOSED for source decision predicate and alpha identity | none | `higham11_1_BunchParlettCompletePivotChoice`, `higham11_1_bunch_parlett_alpha_root` |
| H11.1-growth | pp. 215-216 | precise prose/bound | Complete-pivoting growth and multiplier bounds | WAIT-PREVIOUS-SPLIT | Yes, indirect: relies on Split 1 norm/growth support and a full recursive pivot trace not locally available | `higham11_1_bunch_parlett_growth_bound`, `higham11_1_bunch_parlett_L_bound` are interfaces only |
| (11.4) | p. 216 | numbered equation | 2 by 2 Schur entry formula | CLOSED | none | `higham11_4_twoByTwoSchurEntry` |
| Alg 11.2 | p. 217 | algorithm | Bunch-Kaufman partial-pivoting first-stage branches | CLOSED for branch predicate | none | `higham11_2_BunchKaufmanPartialPivotCase` |
| (11.5) | p. 218 | numbered equation | 2 by 2 pivot solve backward-error model | WAIT-PREVIOUS-SPLIT | Yes, direct: Split 1 `H02.rounding_model` and `H03.gamma_theta`; exact `O(u^2)` framework must not be reproved locally | `higham11_5_twoByTwoPivotSolveStable` is first-order predicate only |
| Thm 11.3 | p. 218 | theorem | General block LDLT factor/solve backward error | WAIT-PREVIOUS-SPLIT | Yes, direct: Split 1 FP/gamma/componentwise-error families; indirect: requires (11.5) and concrete block-LDLT rounded loop | `higham11_3_block_ldlt_backward_error_interface` is an interface, not closure |
| (11.6) | p. 219 | numbered equation/symbolic example | Partial-pivoting example with unbounded `L` | CLOSED | none | `higham11_6_partialPivotExample_factorization` |
| Thm 11.4 | p. 219 | theorem | Bunch-Kaufman solve backward stability | WAIT-PREVIOUS-SPLIT | Yes, direct: Split 1 max-entry/norm and FP gamma families; indirect: Theorem 11.3 and growth bridge | `higham11_4_bunch_kaufman_*` are interfaces |
| Alg 11.5 | p. 220 | algorithm | Symmetric rook pivoting first-stage accepted-pivot predicate | CLOSED for accepted-pivot tests | none | `higham11_5_SymmetricRookFirstPivotChoice` |
| H11-rook-props | pp. 220-221 | precise prose/bounds | Rook `L` entry, 2 by 2 condition, growth, and Theorem 11.4 inheritance | WAIT-PREVIOUS-SPLIT | Yes, indirect: Split 1 norm/growth foundations and Theorem 11.4 gate | `higham11_5_rookPivotLBound`, `higham11_5_rookPivotTwoByTwoCondBound` are predicates |
| (11.7) | p. 221 | numbered equation | Rook/partial forward-error bound | WAIT-PREVIOUS-SPLIT | Yes, direct: Split 1 condition-number/norm tools; indirect: block-LDLT rounded solve theorem | `higham11_7_forwardErrorBound` is source predicate only |
| Alg 11.6 | p. 221 | algorithm | Bunch tridiagonal pivot-size strategy | CLOSED for first-stage decision and alpha identity | none | `higham11_6_BunchTridiagonalPivotChoice`, `higham11_6_bunch_tridiagonal_alpha_root` |
| (11.8) | p. 222 | numbered equation | Tridiagonal block LDLT factorization spec | CLOSED as source spec | none | `higham11_8_tridiagonalBlockLDLTSpec` |
| Thm 11.7 | p. 222 | theorem | Tridiagonal block LDLT backward stability | WAIT-PREVIOUS-SPLIT | Yes, direct: Split 1 FP/gamma and max-entry norm families; indirect: 2 by 2 solve analysis | `higham11_7_tridiagonal_backward_error_interface` is an interface |
| (11.9) | p. 222 | numbered equation | Normwise tridiagonal backward-error bound | WAIT-PREVIOUS-SPLIT | Yes, direct: Split 1 FP/gamma and norm foundations | covered by the interface above |
| (11.10) | p. 222 | numbered equation | Aasen `H = T L^T` | CLOSED | none | `higham11_10_aasenH` |
| (11.11) | p. 223 | numbered equation | Expanded Aasen column recurrence | CLOSED at matrix-equation level | none | covered by `higham11_10_aasenH`; expanded display not duplicated |
| (11.12) | p. 223 | numbered equation | Aasen diagonal equation | CLOSED | none | `higham11_12_aasenDiagonalEquation` |
| (11.13) | p. 223 | numbered equation | Aasen subdiagonal equation | CLOSED | none | `higham11_13_aasenSubdiagonalEquation` |
| (11.14) | p. 223 | numbered equation | Aasen next-column update | CLOSED | none | `higham11_14_aasenNextColumnEquation` |
| (11.15) | p. 223 | numbered equation | Aasen solve chain | CLOSED | none | `higham11_15_aasenSolveChain` |
| Thm 11.8 | p. 224 | theorem | Aasen backward error and normwise bound | WAIT-PREVIOUS-SPLIT | Yes, direct: Split 1 FP/gamma/norm families; indirect: GEPP/tridiagonal solve and Aasen rounded loop | `higham11_8_aasen_backward_error_interface`, `higham11_8_aasenNormwiseBackwardBound` are interfaces |
| H11-aasen-growth | p. 224 | precise prose/bound | Aasen growth `rho_n <= 4^(n-2)` and experiments | WAIT-PREVIOUS-SPLIT for bound; SKIP for experiments | Bound: Yes, indirect via norm/growth foundations. Experiments: no previous-split dependency; empirical output skipped | `higham11_8_aasenGrowthBound`; empirical rows skipped |
| H11-compare-methods | pp. 224-225 | prose/comparison | Aasen versus block LDLT library/use comparison | SKIP | No previous-split dependency | literature/software comparison, no theorem-level target |
| H11-skew-basic | p. 225 | precise prose | Skew-symmetric diagonal is zero | CLOSED | none | `higham11_16_skew_diag_zero` |
| H11-skew-spectral | p. 225 | precise prose | Skew eigenvalue pairing and odd-order singularity | WAIT-PREVIOUS-SPLIT | Yes, direct: Split 1 spectral/eigenvalue foundations | not formalized |
| (11.16) | p. 225 | numbered equation | Skew block LDLT factorization spec and skew Schur complement | CLOSED as spec/definition | none | `higham11_16_SkewBlockLDLTSpec`, `higham11_16_skewSchurComplement` |
| Alg 11.9 | p. 225 | algorithm | Bunch pivot strategy for skew-symmetric matrices | CLOSED for first-stage pivot predicate | none | `higham11_9_SkewBunchPivotChoice` |
| H11-skew-growth | p. 226 | precise prose/bounds | Skew `L` bound, Schur-entry bound, growth `(sqrt 3)^(n-2)` | WAIT-PREVIOUS-SPLIT | Yes, indirect: Split 1 norm/growth foundations and recursive pivot trace | predicate/interface declarations only |
| H11-notes | pp. 226-228 | notes/LAPACK | references, software routine names, library history | SKIP | No previous-split dependency | literature/software material |

## Problem Ledger

| Problem | Classification | Previous-split dependency | Lean artifact/status |
|---|---|---|---|
| 11.1 | CLOSED | none | `higham11_problem_11_1_zero_of_symmetric_singular_principal_pivots` |
| 11.2 determinant and overflow-safe inverse subclaims | CLOSED | none | `higham11_problem_11_2_det_negative_of_pivot_bound`, `higham11_problem_11_2_twoByTwoPivot_scaledInverse_spec` |
| 11.2 inertia/eigenvalue subclaim | WAIT-PREVIOUS-SPLIT | Yes, direct: Split 1 spectral/eigenvalue/inertia foundations | `higham11_problem_11_2_inertiaFormula` predicate only |
| 11.3 | CLOSED as source decision predicate | none | `higham11_problem_11_3_twoByTwoPartialPivoting` |
| 11.4 no 2 by 2 SPD pivot subclaim | CLOSED | none | `higham11_problem_11_4_spd_no_negative_twoByTwo_principal_det`; reuses Chapter 10 `higham10_problem_10_1_two_by_two_minor_pos` |
| 11.4 full factorization outcome | WAIT-PREVIOUS-SPLIT | Yes, indirect: uses Problem 11.2 inertia/eigenvalue foundation and full Algorithm 11.2 trace | `higham11_problem_11_4_spdPartialPivotingOutcome` predicate only |
| 11.5 | WAIT-PREVIOUS-SPLIT | Yes, direct: Split 1 FP rounding/gamma; indirect: GEPP exact 2 by 2 solve path | `higham11_5_twoByTwoPivotSolveStable` first-order predicate only |
| 11.6 | SKIP | No previous-split dependency | MATLAB-generated comparison-count exercise; classified as benchmark/cost-model material until an executable rook-loop comparison counter exists |
| 11.7 SPD no-interchange algebra | CLOSED | none | `higham11_problem_11_7_modifiedOmega_second_test_from_spd_minor` |
| 11.7 unchanged growth-bound subclaim | WAIT-PREVIOUS-SPLIT | Yes, indirect: depends on full Algorithm 11.2/11.5 growth analysis and Split 1 norm foundations | not closed |
| 11.8 | CLOSED | none | `higham11_problem_11_8_rookCompleteExample_factorization` |
| 11.9(a) | CLOSED | none | `higham11_problem_11_9_quasidefinite_kernel_trivial` proves kernel-trivial nonsingularity from the two block equations |
| 11.9(b) | WAIT-PREVIOUS-SPLIT | Yes, indirect: needs determinant/invertibility/leading-principal-minor foundations plus LU-existence surface | not closed |
| 11.9(c) | CLOSED as reduction | none | `higham11_problem_11_9_signed_block_quadratic_pos` proves the concrete signed-block quadratic form; `higham11_problem_11_9_nonsymPosDef_of_symPartSPD` reuses the Chapter 10 symmetric-part bridge |
| 11.10 | SKIP | No previous-split dependency | research problem, no determinate theorem statement |

## Formalized End-To-End Without Unresolved Previous-Split Blocking

| Source label/name | Lean declaration(s) | File | Newly proved or reused | Genuine proof-chain confirmation |
|---|---|---|---|---|
| Bunch-Parlett alpha root | `higham11_1_bunch_parlett_alpha_root` | `HighamChapter11.lean` | reused from existing Chapter 11 pass | algebraic proof over `sqrt 17` |
| Bunch tridiagonal alpha root | `higham11_6_bunch_tridiagonal_alpha_root` | same | reused | algebraic proof over `sqrt 5` |
| Equation (11.6) partial-pivoting factorization | `higham11_6_partialPivotExample_factorization` | same | reused | finite 3 by 3 matrix multiplication proof |
| Skew-symmetric diagonal zero | `higham11_16_skew_diag_zero` | same | reused | direct proof from `A i i = -A i i` |
| Problem 11.1 | `higham11_problem_11_1_zero_of_symmetric_singular_principal_pivots` | same | newly proved | determinant algebra, no hypothesis equivalent to conclusion |
| Problem 11.2 inverse formula | `higham11_problem_11_2_twoByTwoPivot_scaledInverse_spec` | same | newly proved | finite 2 by 2 inverse multiplication proof |
| Problem 11.2 determinant negativity | `higham11_problem_11_2_det_negative_of_pivot_bound` | same | newly proved | inequality proof from `alpha^2 < 1` and nonzero scale |
| Problem 11.4 SPD no-negative-pivot determinant | `higham11_problem_11_4_spd_no_negative_twoByTwo_principal_det` | same | newly proved | uses already proved Chapter 10 SPD principal-minor theorem |
| Problem 11.7 modified-omega second-test algebra | `higham11_problem_11_7_modifiedOmega_second_test_from_spd_minor` | same | newly proved | scalar inequality proof from positive principal minor |
| Problem 11.8 complete/rook factorization | `higham11_problem_11_8_rookCompleteExample_factorization` | same | newly proved | finite 3 by 3 matrix multiplication proof |
| Problem 11.9(a) kernel-trivial nonsingularity | `higham11_problem_11_9_quasidefinite_kernel_trivial` | same | newly proved | block-row equations multiplied by the split vectors; cross terms cancel; SPD quadratic forms force both vector parts to vanish |
| Problem 11.9(c) signed-block reduction | `higham11_problem_11_9_signed_block_quadratic_pos`, `higham11_problem_11_9_nonsymPosDef_of_symPartSPD` | same | newly proved / reused | concrete signed-block quadratic proof plus Chapter 10 equivalence between nonsymmetric PD and SPD symmetric part |

## Formalized End-To-End While Relying On Previous-Split Results

No Chapter 11 row was newly closed by relying on an already implemented previous-split result in this pass. Existing and new closed rows use local Split 2 code, Mathlib real algebra, or earlier same-split Chapter 10 results.

## Not Formalized Because Of Previous-Split Dependency

| Source label/name | Direct or indirect dependency | Previous split | Exact contract family or missing result | Why not reproved locally | Next expected upstream theorem/interface |
|---|---|---|---|---|---|
| Intro eigenvalue/inertia equivalences; Sylvester inertia theorem | direct | 1 | `H06.svd` / spectral theorem / inertia API | foundational spectral theory belongs to Split 1 | reusable real symmetric eigenvalue and inertia theorems |
| (11.5), Theorem 11.3, Problem 11.5 | direct plus indirect | 1 | `H02.rounding_model`, `H03.gamma_theta`, componentwise FP solve bounds | Chapter 11 must not locally axiomatize or duplicate FP/gamma foundations | end-to-end 2 by 2 GEPP/explicit-inverse solve backward-error theorem |
| Theorem 11.4 and (11.7) | direct plus indirect | 1 | `H06.norms`, `H03.gamma_theta`, max-entry/growth-factor bridges | depends on upstream norm/FP calculus and Theorem 11.3 | proved Bunch-Kaufman growth and solve backward-error theorem |
| Theorem 11.7 and (11.9) | direct plus indirect | 1 | `H03.gamma_theta`, max-entry norm tools | finite-precision tridiagonal block LDLT analysis depends on upstream FP model | rounded tridiagonal block LDLT stability theorem |
| Theorem 11.8 | direct plus indirect | 1 | `H03.gamma_theta`, norm and GEPP solve bounds | Aasen rounded-loop proof must instantiate upstream FP/gamma results | Aasen componentwise and normwise backward-error theorem |
| Skew eigenvalue pairing and odd-dimensional singularity | direct | 1 | spectral/eigenvalue foundations | belongs with Split 1 norm/SVD/eigen infrastructure | skew-symmetric spectral-pairing theorem |
| Skew growth and stability prose | indirect | 1 | norm/growth-factor foundations plus recursive pivot trace | should be proved against shared norm/growth APIs, not redefined locally | recursive skew block LDLT growth theorem |
| Problem 11.2 inertia subclaim | direct | 1 | eigenvalue/inertia API for symmetric `2 x 2` blocks | determinant negativity alone is local; eigenvalue-count conclusion is spectral | theorem that a real symmetric 2 by 2 block with negative determinant has inertia `(1,1,0)` |
| Problem 11.4 full SPD factorization outcome | indirect | 1 | Problem 11.2 inertia plus full Algorithm 11.2 trace | cannot close algorithm-level claim until pivot trace and inertia theorem are available | no-2-by-2-pivot theorem for SPD Bunch-Kaufman trace |
| Problem 11.7 unchanged growth bound | indirect | 1 | growth-factor proof for modified strategy | scalar SPD no-interchange part is closed; growth proof belongs with pivot-growth API | modified-omega growth theorem |
| Problem 11.9(b) | indirect | 1 | determinant/invertibility/leading-principal-minor foundations plus LU-existence surface | the source claim is about every permutation and LU existence, which should reuse shared principal-submatrix and LU-existence APIs | leading-principal-minor nonsingularity theorem for arbitrary permuted symmetric quasidefinite matrices |

## Not Formalized For Another Reason

| Source label/name | Classification | Previous-split dependency | Exact reason | Destination |
|---|---|---|---|---|
| Quotes, historical notes, references, LAPACK routine lists | SKIP | No previous-split dependency | editorial/literature/software material | none |
| Aasen direct-search numerical values for `n=4,5` | SKIP | No previous-split dependency | empirical output from reported optimization runs | benchmark mode only |
| Method-speed comparisons in §11.2.1 | SKIP | No previous-split dependency | qualitative/literature comparison, no precise theorem | none |
| Problem 11.6 comparison-count MATLAB family | SKIP | No previous-split dependency | cost-model/programming-language exercise requiring executable comparison counter; treated as benchmark/cost-model material, not core proof | future benchmark/cost-model pass |
| Problem 11.10 | SKIP | No previous-split dependency | explicit research problem | none |

## Hidden-Hypothesis Summary

Final-facing new theorem hypotheses are source/domain assumptions:

- Problem 11.1 assumes symmetry and singularity of all 1 by 1 and 2 by 2 principal pivots.
- Problem 11.2 inverse formula assumes the scaled denominator is nonzero.
- Problem 11.2 determinant negativity assumes the source pivot-bound inequality, `alpha^2 < 1`, and a nonzero pivot scale.
- Problem 11.4 assumes SPD and distinct indices.
- Problem 11.7 assumes the positive 2 by 2 principal minor, domination `a_rr <= omega_r`, and `alpha <= 1`.
- Problem 11.8 is unconditional in `epsilon`.
- Problem 11.9(a) assumes the two block kernel equations for `[[H,B^T],[B,-G]]` and SPD of `H` and `G`.
- Problem 11.9(c) assumes SPD of `H` and `G` for the concrete signed-block quadratic theorem; the generic wrapper assumes the symmetric part is SPD, exactly matching the Chapter 10 bridge theorem.

No new theorem assumes its own conclusion, a stability theorem, a growth theorem, or a hidden good event. Interface rows from the earlier pass remain explicitly classified as not closed.

## Weak Components And Bottlenecks

Weak components checked:

| Component | Why weak | Checks | Status |
|---|---|---|---|
| Problem 11.2 inverse formula | division-heavy 2 by 2 algebra | Lean theorem type; finite multiplication proof; axiom check planned | closed |
| Problem 11.7 scalar inequality | source uses chained strict/non-strict inequalities | Lean theorem type; compared with Appendix A displayed inequality | closed |
| Problem 11.8 factorization | source extraction corrupted the matrix layout | rendered Appendix A page inspected; Lean finite matrix proof | closed |
| Problem 11.9 block algebra | source uses block matrices not directly modeled as one repository matrix type | Lean theorem type; Appendix A block equations compared; split-vector proof avoids a new parallel matrix API | closed for 11.9(a,c), open for 11.9(b) |
| Theorem 11.3/11.4/11.7/11.8 interfaces | easy to overclaim | report marks them `WAIT-PREVIOUS-SPLIT`, not completed | open, honest |

Active bottleneck: Chapter 11 stability theorems require Split 1 FP/gamma/norm foundations and Split 2 executable pivot traces. No downstream theorem in this report is counted as closing those rows.

## Verification

Commands run in this pass:

- `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` before edits: passed.
- `lake env lean LeanFpAnalysis/FP/Algorithms/Cholesky/CholeskyIndefinite.lean` before edits: passed.
- `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter11.lean` after Problem 11.9 follow-up edits: passed.
- `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter11 LeanFpAnalysis.FP.Algorithms`: passed. It replayed only pre-existing QR/FastMatMul warnings outside Chapter 11.
- `lake env lean examples/LibraryLookup.lean`: failed with the already observed stack overflow in the IEEE `#check` section before the Chapter 11 checks. This is not caused by the Chapter 11 additions.
- Focused Chapter 11 lookup via stdin `#check`: passed for `higham11_problem_11_9_quasidefinite_kernel_trivial` and `higham11_problem_11_9_signed_block_quadratic_pos`.
- Code-only placeholder scan over `HighamChapter11.lean`, `CholeskyIndefinite.lean`, and `examples/LibraryLookup.lean`: no `sorry`, `admit`, `axiom`, or `unsafe` matches.
- `#print axioms` for the new Problem 11.9 final-facing theorems: each depends only on standard Lean/mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`.
- `git diff --check`: passed.
- `lake build`: passed, 3476 jobs. It replayed only pre-existing QR/FastMatMul linter warnings outside Chapter 11.
- Orphan-class/vacuous-definition audit: no orphan class hypotheses and no vacuous definitions were introduced; the new Problem 11.9 artifacts are theorems over explicit source/domain assumptions.

## Documentation

- Inventory/report path: `chapter_splitting/reports/chapter11_formalization_report.md`.
- Lookup paths updated: `docs/LIBRARY_LOOKUP.md`, `examples/LibraryLookup.lean`.
- No theorem note or PDF generated.
