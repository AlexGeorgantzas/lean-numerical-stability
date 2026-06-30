# Higham Chapter 19 Source Coverage Ledger

## Source and Scope

- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002), inferred from the repository's SIAM DOI chapter PDF path and the shared chapter index. Local `pdfinfo` is not installed in this environment.
- Chapter: 19, "QR Factorization".
- Source file: `References/1.9780898718027.ch19.pdf`.
- Mode: core.
- Parallel split: 3B.
- Planning documents consulted: `chapter_splitting/HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md`, Split 3B section of `chapter_splitting/split_primary_contracts.md`, and the Chapter 19 rows of `chapter_splitting/chapter_index.md`.
- Selected-scope gate: FAIL. Chapter 19 has substantial QR infrastructure and checked source-facing wrappers, but the full selected core pass is not complete. The currently active QR route is the arbitrary-width stored Householder final-panel bridge for Theorem 19.13 support; source-closure data can now be assembled directly from actual stage-two/stage-three twice-trailing source-tail facts, and the full pivot-2 double-zero-prefix extraction now produces the one-column/source-tail vector and self-dot facts. The remaining full-loop work is the arbitrary-width stage-three extraction and determinant threading needed by the first-two source-tail constructor.
- Inventory status: starter ledger only. The shared `chapter_index.md` accounts for the primary labels, numbered equations, and problems, but this tracked Ch19 report still needs a full row-by-row inventory before chapter completion can be claimed.
- Oracle status: GPT Pro/Oracle browser consultation was attempted for the repeated stored-loop-to-source-closure bottleneck on 2026-06-30 with a compact math-only packet. The run failed without a mathematical answer after Chrome became unreachable, and the visible prompt captured by Oracle was only the packet title, so it is recorded as a rejected/non-answer consultation rather than proof-source evidence.

## Progress Snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| ch19 | core | 90 | 99 | 99 | 99 | 99 | 95 | 48+ | Derive stage-three source reflector facts from the full stored loop | medium |

## Current Ch19 Closure-Data Route

| Source target | Lean declaration | File | Status | Notes |
|---|---|---|---|---|
| Theorem 19.13 support, stored Householder final-panel route | `H19.Theorem19_13.storedSignedSequenceTwiceTrailingClosureData` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | partial foundation | Recursive data contract for arbitrary-width twice-trailing closure. |
| Theorem 19.13 support, arbitrary tail closure | `H19.Theorem19_13.storedSignedSequenceTwiceTrailingFinalClosed_of_closureData` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | proved dependency | Turns recursive closure data into the named twice-trailing final-panel closure predicate. |
| Theorem 19.13 support, final-panel bridge | `H19.Theorem19_13.storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_closureData` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | proved dependency | Consumes recursive closure data plus first two stored-reflector facts to prove the arbitrary-width final-panel equality. |
| Theorem 19.13 support, source-closure final-panel bridge | `H19.Theorem19_13.storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_sourceClosureData` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | proved dependency | Directly consumes the raw recursive source-closure contract by composing it with `storedSignedSequenceTwiceTrailingClosureData_of_sourceClosureData`, so the remaining stored-loop induction can target source-closure data itself. |
| Theorem 19.13 support, closure-data constructors | `H19.Theorem19_13.storedSignedSequenceTwiceTrailingClosureData_zero`; `..._one_of_reflectorData`; `..._one_of_tail_reflector_self_dot`; `..._succ_succ_of_firstTwoReflectorData`; `..._succ_succ_of_reflector_self_dot`; `..._succ_succ_of_tail_reflector_self_dot` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | proved dependency | Constructor API for the stored-loop induction target, including explicit one-column, abstract two-step, and raw twice-trailing tail reflector-fact entry points. |
| Theorem 19.13 support, source closure facts | `H19.Theorem19_13.storedSignedSequenceOneTailReflectorFacts`; `...FirstTwoTailReflectorFacts`; `...TwiceTrailingSourceClosureData`; `...TwiceTrailingClosureData_of_sourceClosureData` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | proved dependency | Recursive source-facing contract that stores raw stage-2/stage-3 twice-trailing tail facts and proves they imply the existing recursive closure-data package. |
| Theorem 19.13 support, stage-fact packagers | `H19.Theorem19_13.storedSignedSequenceOneTailReflectorFacts_of_twice_trailing_stage_facts`; `...FirstTwoTailReflectorFacts_of_twice_trailing_stage_facts` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | proved dependency | Packages actual stage-two/stage-three twice-trailing stored-loop facts into the raw source-tail contracts. The two-step theorem uses the stage-two stored recurrence to rewrite the real stage-three source panel into the synthetic `trailingPanel S0` surface, but it does not derive the hard normalized-vector/self-dot facts. |
| Theorem 19.13 support, full stage-two extraction | `H19.Theorem19_13.householderTrailingActiveVector_succ_succ_zeroPrefix_of_succ_succ`; `...tail_eq_of_succ_succ_zeroPrefix`; `...tail_self_dot_of_succ_succ`; `...storedSignedSequenceOneTailReflectorFacts_of_full_stage_two_zero_prefixed_facts`; `...storedSignedSequenceTwiceTrailingSourceClosureData_one_of_full_stage_two_zero_prefixed_facts` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | proved dependency | Extracts twice-trailing source-tail vector equality and self-dot facts from the full pivot-2 active-vector surface when it is double-zero-prefixed, then assembles the one-column source-closure contract. This closes the odd-width/stage-two extraction shape and leaves the stage-three full-loop extraction as the next listed dependency. |
| Theorem 19.13 support, source-closure constructors | `H19.Theorem19_13.storedSignedSequenceTwiceTrailingSourceClosureData_zero`; `...one_of_tail_reflector_facts`; `...one_of_tail_reflector_self_dot`; `...one_of_twice_trailing_stage_facts`; `...succ_succ_of_firstTwoTailReflectorFacts`; `...succ_succ_of_tail_reflector_self_dot`; `...succ_succ_of_twice_trailing_stage_facts` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | proved dependency | Constructor API for the source-facing induction target. The new `...twice_trailing_stage_facts` wrappers consume actual one-column and two-step stage facts directly; the two-step wrapper uses the existing stage-fact packager to rewrite the real stage-three source panel into the synthetic `trailingPanel S0` surface before assembling `storedSignedSequenceTwiceTrailingSourceClosureData`. |
| Theorem 19.13 support, reflector-data packagers | `H19.Theorem19_13.storedSignedSequenceOneReflectorData_of_tail_reflector_self_dot`; `...FirstTwoReflectorData_of_tail_reflector_self_dot`; `...ClosureData_one_of_tail_reflector_self_dot` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | proved dependency | Packages explicit twice-trailing source reflector facts into the recursive closure-data records; existing fixed-width bridges now consume the first-two packager. |
| Theorem 19.13 support, one recursive source-facing step | `H19.Theorem19_13.storedSignedSequence_final_panel_eq_qrPanel_R_of_firstTwoReflectorData_and_tailClosureData` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | proved dependency | If the current twice-trailing tail has first-two reflector data and the twice-shrunk tail has closure data, the final-panel equality follows. |
| Theorem 19.13 support, raw source-tail recursive step | `H19.Theorem19_13.storedSignedSequence_final_panel_eq_qrPanel_R_of_firstTwoTailReflectorFacts_and_tailSourceClosureData` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | proved dependency | Consumes raw first-two twice-trailing source facts plus recursive source closure, assembles source-closure data with the new constructors, and feeds the direct source-closure final-panel bridge. |

## GPT-5.5 Pro Browser Consultations

| Selected claim/blocker | Oracle session/model | Prompt summary | Key route suggested | Adopted/rejected steps | Lean validation | Status |
|---|---|---|---|---|---|---|
| Theorem 19.13 stored-loop-to-source-closure route | `ch19-source-closure`, `gpt-5.5-pro`, browser mode | Intended compact math-only packet asked whether stored-loop hypotheses imply source normalized-vector equality/self-dot and, if not, what corrected theorem surface is source-faithful. | None. Oracle recorded only the packet title as the prompt and then lost Chrome connectivity. | Rejected as non-answer/tool failure; no mathematical advice adopted. Stale Oracle helper processes were stopped. | None from Oracle; local route continued with a proved raw source-tail recursive bridge. | failed/non-answer |

## Open Selected-Scope Items

| Source location | Exact selected claim/status | Current Lean status | Missing foundation | Next concrete theorem |
|---|---|---|---|---|
| Theorem 19.13 support route | Arbitrary-width stored Householder final-panel equality from source loop facts. | Closure-data handoff, direct source-closure final-panel bridge, one recursive source-facing step, explicit reflector-fact packagers, raw one/two-step closure-data constructors, a recursive source-closure-data contract, stage-fact packagers, direct source-closure constructors from actual stage facts, full pivot-2 double-zero-prefix extraction, and a raw source-tail recursive final-panel bridge are proved. | Derive the remaining arbitrary-width stage-three twice-trailing source reflector facts from the full stored loop's per-pivot reflector normalization, self-dot, and determinant nonbreakdown facts. Source-closure data assembly, stage-two extraction, the stage-three synthetic-panel rewrite, and the induction-facing stage-fact constructor wrappers are now closed. | Prove the stored-loop derivation of the stage-three facts consumed by `storedSignedSequenceTwiceTrailingSourceClosureData_succ_succ_of_twice_trailing_stage_facts`, using the new pivot-2 extraction lemmas for the first source-tail stage. |
| Chapter 19 full core inventory | Lemmas 19.1-19.3, 19.7-19.9; Theorems 19.4-19.6, 19.10, 19.13; Algorithms 19.11-19.12; numbered equations and theoretical problems. | Many declarations exist in QR modules, but this tracked report is not yet a complete source inventory. | Full row-by-row source audit against the rendered Chapter 19 PDF. | Complete this ledger's source inventory and update skipped/deferred/benchmark classifications. |

## Skipped, Deferred, and Benchmark Categories

| Category | Status |
|---|---|
| Historical notes, LAPACK/software prose, figures, tables, and empirical output | Skipped in core mode unless a precise theorem-level dependency is identified. |
| Fixed numerical experiments | Skipped in core mode unless needed as an exact witness. |
| Benchmark comparisons | Reserved for benchmark mode; none promoted by this closure-data milestone. |
| Theorem 19.13 fully implementation-facing closure | Deferred until the stored-loop closure-data package is constructed from source-equivalent facts. |

## Weak-Component and Bottleneck Summary

| Component | Why weak | Current evidence | Next listed dependency | Status |
|---|---|---|---|---|
| Theorem 19.13 stored-loop-to-source-closure route | Repeated source-facing floating-point/QR blocker; theorem names can overstate closure if recursive facts are only assumed. | Source-closure final-panel bridge, closure-data conversion, source-closure constructors, stage-fact packagers, induction-facing stage-fact constructor wrappers, full pivot-2 double-zero-prefix extraction, and the raw source-tail recursive final-panel bridge compile, so the remaining gap is no longer data assembly, final-panel handoff, stage-two extraction, or the stage-three synthetic-panel rewrite. | Prove the actual arbitrary-width stage-three normalized-vector, self-dot, and determinant facts from the full stored loop, feeding the existing two-step source-closure wrapper. | active bottleneck |
| New source-closure constructors | Adapter lemmas around a recursive contract; they must be treated as dependency infrastructure, not as closing Theorem 19.13. | The constructors only package explicit raw facts or actual stage facts into `storedSignedSequenceTwiceTrailingSourceClosureData`; the open selected row remains visible above. Their axiom footprint is the standard `propext`, `Classical.choice`, and `Quot.sound`. | Use them inside the full stored-loop induction after the raw facts are proved. | checked dependency |

## Verification

- `lake env lean LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean`: passed after adding the full stage-two double-zero-prefix extraction lemmas and one-column source-closure wrapper.
- `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19`: passed after adding the full stage-two double-zero-prefix extraction lemmas and one-column source-closure wrapper; only pre-existing `GivensSpec` unused-simp warnings were reported.
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean`: no matches after adding the full stage-two double-zero-prefix extraction lemmas and one-column source-closure wrapper.
- `git diff --check`: passed after adding the full stage-two double-zero-prefix extraction lemmas and one-column source-closure wrapper, with only the usual CRLF normalization warning for `Higham19.lean`.
- `#print axioms` for `householderTrailingActiveVector_succ_succ_zeroPrefix_of_succ_succ`, `householderTrailingActiveVector_tail_eq_of_succ_succ_zeroPrefix`, `householderTrailingActiveVector_tail_self_dot_of_succ_succ`, `storedSignedSequenceOneTailReflectorFacts_of_full_stage_two_zero_prefixed_facts`, and `storedSignedSequenceTwiceTrailingSourceClosureData_one_of_full_stage_two_zero_prefixed_facts`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env lean LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean`: passed after adding the induction-facing actual stage-fact source-closure constructors.
- `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19`: passed after adding the induction-facing actual stage-fact source-closure constructors; only pre-existing `GivensSpec` unused-simp warnings were reported.
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean`: no matches after adding the induction-facing actual stage-fact source-closure constructors.
- `git diff --check`: passed after adding the induction-facing actual stage-fact source-closure constructors, with only CRLF normalization warnings for `Higham19.lean` and this report.
- `#print axioms` for `storedSignedSequenceTwiceTrailingSourceClosureData_one_of_twice_trailing_stage_facts` and `storedSignedSequenceTwiceTrailingSourceClosureData_succ_succ_of_twice_trailing_stage_facts`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env lean LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean`: passed after adding the source-closure constructor API.
- `lake env lean LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean`: passed after adding the raw source-tail recursive final-panel bridge.
- `lake env lean LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean`: passed after adding the one-column and first-two actual stage-fact packagers.
- `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19`: passed after adding the source-closure constructor API; only pre-existing `GivensSpec` unused-simp warnings were reported.
- `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19`: passed after adding the raw source-tail recursive final-panel bridge; only pre-existing `GivensSpec` unused-simp warnings were reported.
- `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19`: passed after adding the one-column and first-two actual stage-fact packagers; only pre-existing `GivensSpec` unused-simp warnings were reported.
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean`: no matches after adding the source-closure constructor API.
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean`: no matches after adding the raw source-tail recursive final-panel bridge.
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean`: no matches after adding the one-column and first-two actual stage-fact packagers.
- `git diff --check`: passed after adding the source-closure constructor API, with only CRLF normalization warnings for `Higham19.lean` and this report.
- `git diff --check`: passed after adding the raw source-tail recursive final-panel bridge, with only CRLF normalization warnings for `Higham19.lean` and this report.
- `git diff --check`: passed after adding the one-column and first-two actual stage-fact packagers, with only CRLF normalization warnings for `Higham19.lean` and this report.
- `#print axioms` for `storedSignedSequenceTwiceTrailingSourceClosureData_one_of_tail_reflector_facts`, `storedSignedSequenceTwiceTrailingSourceClosureData_one_of_tail_reflector_self_dot`, and `storedSignedSequenceTwiceTrailingSourceClosureData_succ_succ_of_tail_reflector_self_dot`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `#print axioms` for `storedSignedSequence_final_panel_eq_qrPanel_R_of_firstTwoTailReflectorFacts_and_tailSourceClosureData`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `#print axioms` for `storedSignedSequenceOneTailReflectorFacts_of_twice_trailing_stage_facts` and `storedSignedSequenceFirstTwoTailReflectorFacts_of_twice_trailing_stage_facts`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env lean LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean`: passed for the closure-data constructors, reflector-data packagers, explicit two-step closure-data constructors, recursive source-closure-data contract, one-step bridge milestone, and direct source-closure final-panel bridge.
- `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19`: passed after the direct source-closure final-panel bridge; only pre-existing `GivensSpec` unused-simp warnings were reported.
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean`: no matches.
- `git diff --check`: passed with only CRLF warnings for `Higham19.lean` and this report.
- `#print axioms` for `storedSignedSequence_final_panel_eq_qrPanel_R_of_firstTwoReflectorData_and_tailClosureData` and `storedSignedSequenceTwiceTrailingClosureData_succ_succ_of_firstTwoReflectorData`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `#print axioms` for `storedSignedSequenceOneReflectorData_of_tail_reflector_self_dot`, `storedSignedSequenceFirstTwoReflectorData_of_tail_reflector_self_dot`, and `storedSignedSequenceTwiceTrailingClosureData_one_of_tail_reflector_self_dot`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `#print axioms` for `storedSignedSequenceTwiceTrailingClosureData_succ_succ_of_reflector_self_dot`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `#print axioms` for `storedSignedSequenceTwiceTrailingClosureData_succ_succ_of_tail_reflector_self_dot`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `#print axioms` for `storedSignedSequenceTwiceTrailingClosureData_of_sourceClosureData`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `#print axioms` for `storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_sourceClosureData`: only `propext`, `Classical.choice`, and `Quot.sound`.

## Git and Local-Only Notes

- Work is on shared local `main`, synchronized with `origin/main` before theorem design.
- `chapter_splitting/` is local-only context: it is ignored by `.gitignore`, has no tracked files, and must not be pushed.
- Remaining local untracked file at this point: `.codex/config.toml`.
