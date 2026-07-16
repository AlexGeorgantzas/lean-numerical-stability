# Higham Chapter 27 Formalization Report

## Source and scope

- Edition: 2nd ed., SIAM, 2002.
- Chapter: 27, "Software Issues in Floating Point Arithmetic", pp. 489-509.
- Source file: `References/1.9780898718027.ch27.pdf`.
- Mode / split: core / Split 4.
- Planning documents: full blueprint, Split 4 contract, chapter index.
- Selected-scope gate: **PASS**.

## Completed selected targets

| Source | Lean declarations | Scope |
|---|---|---|
| Sec. 27.1 | `FPException`, `ExceptionFlags`, `raiseException_mono`, `clearException` | reusable sticky-flag specification |
| Secs. 27.5, 27.7.1, 27.7.4 | `ArithmeticParameters`, `PortableArithmeticModel` | reusable portable-model vocabulary |
| Sec. 27.8, p. 499 | `twoPassScaledNorm`, `twoPassScaledNorm_sq`, `twoPassRoundedScaledSum_bounds_and_safe` | exact squared-output correctness plus a concrete conditional round-to-even no-overflow trace |
| Sec. 27.8 / Appendix 27.5 | `scaledSumSqStep`, fold/nonnegativity invariants, `higham27_problem27_5_scaled_norm_correct_sq` | end-to-end exact-arithmetic correctness of the one-pass scaled norm |
| Sec. 27.8, p. 500 | repository `complexVecOneNorm`, `higham27BlasComplexPseudoOneNorm`, comparison theorem | both printed complex one-norm formulas, kept distinct; true norm reused from `Analysis.Norms` |
| (27.1) | `smithDivReal_eq`, `smithDivImag_eq`, `higham27_eq27_1_smith_complex_division` | exact Smith branch identity with explicit `c != 0` domain |
| p. 500 symmetric Smith branch | `smithDivRealSymmetric_eq`, `smithDivImagSymmetric_eq`, `higham27_smith_complex_division_symmetric` | exact analogous identity with explicit `d != 0` domain |
| p. 500 Smith range behavior | both `smith_*_branch_preDivision_safe` theorems and `smith_scaledDenominator_overflows_at_maxFiniteMagnitude` | scoped rounded safety for both branches; unconditional max-finite wording refuted |

## Honest boundary

The printed two-pass algorithm now has a concrete finite round-to-even trace;
its representable-integer and final dimension-capacity premises are explicit
format/input conditions, not assumptions of the conclusion.  Smith's two
rounded branches likewise have proved pre-division range traces.  The source's
unrestricted Smith suggestion cannot hold literally: the printed denominator
equals twice the largest finite magnitude when `c=d=maxFiniteMagnitude`, and
the module proves that counterexample.

Blue's separate three-accumulator result is deferred because the chapter gives
no executable algorithm, thresholds, rounding order, combination logic, or
accuracy inequality.  The exact Hammarling/Problem 27.5 invariant is retained
as a distinct verified algorithm. Historical machines, compiler behavior,
timing tables, software catalogues, and the Patriot incident are classified as
machine-specific, empirical, or literature review.

## Verification

- Target build: `lake build LeanFpAnalysis.FP.Algorithms.SoftwareIssues.Higham27` - PASS.
- Hygiene scan for `sorry`, `admit`, `axiom`, `unsafe`, and `opaque` - PASS (no matches).
- Representative `#print axioms` checks report only Mathlib's standard
  `propext`, `Classical.choice`, and `Quot.sound` axioms.

## Documentation

- Inventory: `docs/chapter27/CHAPTER27_SOURCE_INVENTORY.md`
- Not-proved ledger: `docs/chapter27/CHAPTER27_NOT_PROVED_LEDGER.md`
- Proof-source ledger: `docs/chapter27/CHAPTER27_PROOF_SOURCE_LEDGER.md`
