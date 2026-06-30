# Higham Chapter 19 Source Coverage Ledger

## Source and Scope

- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002), inferred from the repository's SIAM DOI chapter PDF path and the shared chapter index. Local `pdfinfo` is not installed in this environment.
- Chapter: 19, "QR Factorization".
- Source file: `References/1.9780898718027.ch19.pdf`.
- Mode: core.
- Parallel split: 3B.
- Planning documents consulted: `chapter_splitting/HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md`, Split 3B section of `chapter_splitting/split_primary_contracts.md`, and the Chapter 19 rows of `chapter_splitting/chapter_index.md`.
- Selected-scope gate: FAIL. Chapter 19 has substantial QR infrastructure and checked source-facing wrappers, but the full selected core pass is not complete. The currently active QR route is the arbitrary-width stored Householder final-panel bridge for Theorem 19.13 support; it still needs construction of recursive closure data from the full stored loop's reflector-normalization and determinant facts.
- Inventory status: starter ledger only. The shared `chapter_index.md` accounts for the primary labels, numbered equations, and problems, but this tracked Ch19 report still needs a full row-by-row inventory before chapter completion can be claimed.
- Oracle status: no GPT Pro or external proof-source consultation was used for the closure-data milestones recorded here.

## Progress Snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| ch19 | core | 90 | 99 | 99 | 99 | 99 | 95 | 48+ | Construct `storedSignedSequenceTwiceTrailingClosureData` from the full stored loop | medium |

## Current Ch19 Closure-Data Route

| Source target | Lean declaration | File | Status | Notes |
|---|---|---|---|---|
| Theorem 19.13 support, stored Householder final-panel route | `H19.Theorem19_13.storedSignedSequenceTwiceTrailingClosureData` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | partial foundation | Recursive data contract for arbitrary-width twice-trailing closure. |
| Theorem 19.13 support, arbitrary tail closure | `H19.Theorem19_13.storedSignedSequenceTwiceTrailingFinalClosed_of_closureData` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | proved dependency | Turns recursive closure data into the named twice-trailing final-panel closure predicate. |
| Theorem 19.13 support, final-panel bridge | `H19.Theorem19_13.storedSignedSequence_final_panel_eq_qrPanel_R_of_reflector_self_dot_of_closureData` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | proved dependency | Consumes recursive closure data plus first two stored-reflector facts to prove the arbitrary-width final-panel equality. |
| Theorem 19.13 support, closure-data constructors | `H19.Theorem19_13.storedSignedSequenceTwiceTrailingClosureData_zero`; `..._one_of_reflectorData`; `..._one_of_tail_reflector_self_dot`; `..._succ_succ_of_firstTwoReflectorData`; `..._succ_succ_of_reflector_self_dot`; `..._succ_succ_of_tail_reflector_self_dot` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | proved dependency | Constructor API for the stored-loop induction target, including explicit one-column, abstract two-step, and raw twice-trailing tail reflector-fact entry points. |
| Theorem 19.13 support, source closure facts | `H19.Theorem19_13.storedSignedSequenceOneTailReflectorFacts`; `...FirstTwoTailReflectorFacts`; `...TwiceTrailingSourceClosureData`; `...TwiceTrailingClosureData_of_sourceClosureData` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | proved dependency | Recursive source-facing contract that stores raw stage-2/stage-3 twice-trailing tail facts and proves they imply the existing recursive closure-data package. |
| Theorem 19.13 support, reflector-data packagers | `H19.Theorem19_13.storedSignedSequenceOneReflectorData_of_tail_reflector_self_dot`; `...FirstTwoReflectorData_of_tail_reflector_self_dot`; `...ClosureData_one_of_tail_reflector_self_dot` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | proved dependency | Packages explicit twice-trailing source reflector facts into the recursive closure-data records; existing fixed-width bridges now consume the first-two packager. |
| Theorem 19.13 support, one recursive source-facing step | `H19.Theorem19_13.storedSignedSequence_final_panel_eq_qrPanel_R_of_firstTwoReflectorData_and_tailClosureData` | `LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean` | proved dependency | If the current twice-trailing tail has first-two reflector data and the twice-shrunk tail has closure data, the final-panel equality follows. |

## Open Selected-Scope Items

| Source location | Exact selected claim/status | Current Lean status | Missing foundation | Next concrete theorem |
|---|---|---|---|---|
| Theorem 19.13 support route | Arbitrary-width stored Householder final-panel equality from source loop facts. | Closure-data handoff, one recursive source-facing step, explicit reflector-fact packagers, raw one/two-step closure-data constructors, and a recursive source-closure-data contract are proved. | Construct the source-closure-data contract from the full stored loop's per-pivot reflector normalization, self-dot, and determinant nonbreakdown facts. | `storedSignedSequenceTwiceTrailingSourceClosureData_of_stored_loop_reflector_data`, feeding `storedSignedSequenceTwiceTrailingClosureData_of_sourceClosureData`. |
| Chapter 19 full core inventory | Lemmas 19.1-19.3, 19.7-19.9; Theorems 19.4-19.6, 19.10, 19.13; Algorithms 19.11-19.12; numbered equations and theoretical problems. | Many declarations exist in QR modules, but this tracked report is not yet a complete source inventory. | Full row-by-row source audit against the rendered Chapter 19 PDF. | Complete this ledger's source inventory and update skipped/deferred/benchmark classifications. |

## Skipped, Deferred, and Benchmark Categories

| Category | Status |
|---|---|
| Historical notes, LAPACK/software prose, figures, tables, and empirical output | Skipped in core mode unless a precise theorem-level dependency is identified. |
| Fixed numerical experiments | Skipped in core mode unless needed as an exact witness. |
| Benchmark comparisons | Reserved for benchmark mode; none promoted by this closure-data milestone. |
| Theorem 19.13 fully implementation-facing closure | Deferred until the stored-loop closure-data package is constructed from source-equivalent facts. |

## Verification

- `lake env lean LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean`: passed for the closure-data constructors, reflector-data packagers, explicit two-step closure-data constructors, recursive source-closure-data contract, and one-step bridge milestone.
- `lake build LeanFpAnalysis.FP.Algorithms.QR.Higham19`: passed after the recursive source-closure-data contract milestone; only pre-existing `GivensSpec` unused-simp warnings were reported.
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/QR/Higham19.lean`: no matches.
- `git diff --check`: passed with only CRLF warnings for `Higham19.lean` and this report.
- `#print axioms` for `storedSignedSequence_final_panel_eq_qrPanel_R_of_firstTwoReflectorData_and_tailClosureData` and `storedSignedSequenceTwiceTrailingClosureData_succ_succ_of_firstTwoReflectorData`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `#print axioms` for `storedSignedSequenceOneReflectorData_of_tail_reflector_self_dot`, `storedSignedSequenceFirstTwoReflectorData_of_tail_reflector_self_dot`, and `storedSignedSequenceTwiceTrailingClosureData_one_of_tail_reflector_self_dot`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `#print axioms` for `storedSignedSequenceTwiceTrailingClosureData_succ_succ_of_reflector_self_dot`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `#print axioms` for `storedSignedSequenceTwiceTrailingClosureData_succ_succ_of_tail_reflector_self_dot`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `#print axioms` for `storedSignedSequenceTwiceTrailingClosureData_of_sourceClosureData`: only `propext`, `Classical.choice`, and `Quot.sound`.

## Git and Local-Only Notes

- Work is on shared local `main`, synchronized with `origin/main` before theorem design.
- `chapter_splitting/` is local-only context: it is ignored by `.gitignore`, has no tracked files, and must not be pushed.
- Remaining local untracked file at this point: `.codex/config.toml`.
