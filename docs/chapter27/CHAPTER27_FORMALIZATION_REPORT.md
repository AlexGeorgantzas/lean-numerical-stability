# Higham Chapter 27 Formalization Report

## Source and scope

- Edition: 2nd ed., SIAM, 2002.
- Chapter: 27, "Software Issues in Floating Point Arithmetic", pp. 489-509.
- Source file: `References/1.9780898718027.ch27.pdf`.
- Mode / split: core / Split 4.
- Planning documents: full blueprint, Split 4 contract, chapter index.
- Selected-scope gate: **PASS**.
- Canonical entry point: `NumStability.Source.Higham.Chapter27`; the
  declaration-bearing owners are `Chapter27.SoftwareEnvironment` and
  `Chapter27.Problem06`. The former `Algorithms.SoftwareIssues.Higham27*`
  paths are compatibility imports only.

## Completed selected targets

| Source | Lean declarations | Scope |
|---|---|---|
| Sec. 27.1 | `FPException`, `ExceptionFlags`, `raiseException_mono`, `clearException` | reusable sticky-flag specification |
| Secs. 27.5, 27.7.1, 27.7.4 | `ArithmeticParameters`, `PortableArithmeticModel` | reusable portable-model vocabulary |
| Sec. 27.8, p. 499 | `twoPassScaledNorm`, `twoPassScaledNorm_sq`, `twoPassRoundedScaledNorm`, `higham27_twoPassRoundedScaledNorm_trace_safe` | exact squared-output correctness plus a literal conditional round-to-even returned-norm trace |
| Sec. 27.8 / Appendix 27.5 | `scaledSumSqStep`, fold/nonnegativity invariants, `higham27_problem27_5_scaled_norm_correct_sq` | end-to-end exact-arithmetic correctness of the one-pass scaled norm |
| Sec. 27.8, p. 500 | repository `complexVecOneNorm`, `higham27BlasComplexPseudoOneNorm`, comparison theorem | both printed complex one-norm formulas, kept distinct; true norm reused from `Analysis.Norms` |
| (27.1) | `smithDivReal_eq`, `smithDivImag_eq`, `higham27_eq27_1_smith_complex_division` | exact Smith branch identity with explicit `c != 0` domain |
| p. 500 symmetric Smith branch | `smithDivRealSymmetric_eq`, `smithDivImagSymmetric_eq`, `higham27_smith_complex_division_symmetric` | exact analogous identity with explicit `d != 0` domain |
| p. 500 Smith range behavior | both `smith_*_branch_preDivision_safe` theorems and `smith_scaledDenominator_overflows_at_maxFiniteMagnitude` | scoped rounded safety for both branches; unconditional max-finite wording refuted |
| Problem 27.6 | `higham27_problem27_6_halley_specialization`, `_pair_step_eq_halley`, `_pair_step_invariant`, `_matlab_scaled_step`, `_cubic_error_identity`, `_monotone_enclosure`, `_cubic_error_bound` | exact Moler--Morrison/Halley specialization, scaled recurrence, Pythagorean invariant, monotone enclosure, and cubic error algebra |

## Honest boundary

The printed two-pass algorithm now has a literal finite round-to-even executor:
its zero-scale branch returns before division, while its nonzero branch rounds
the quotient, square, accumulator addition, square root, and final multiply.
Its finite-input, representable-integer, representable-square-root-envelope,
and final-capacity premises are explicit format/input conditions, not
assumptions of trace safety.  The proved certificate records nonzero division
and nonnegative square-root domains as well as every overflow-sensitive exact
pre-round value.  It does not claim that underflow or inexact rounding is
absent.  Smith's two
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

All owned Appendix rows 27.1, 27.3, 27.4, 27.5, 27.7, and 27.8 are inventoried.
Appendix 27.4's defective-generator and underflow trace is an optional,
historical machine-specific row and is not selected; Appendix 27.5 supplies the
exact scaled-norm invariant proved above.

Problem 27.6's exact real-arithmetic content is therefore closed. The only
deferred part is the source's machine-dependent assertion that MATLAB's
`r + 4 == 4` test stops within three iterations; that needs a concrete format
and expression-evaluation semantics.

## Verification

- Historical pre-migration target build:
  `lake build NumStability.Algorithms.SoftwareIssues.Higham27` - PASS. That
  path is now a compatibility wrapper; the canonical targets are
  `NumStability.Source.Higham.Chapter27`,
  `NumStability.Source.Higham.Chapter27.SoftwareEnvironment`, and
  `NumStability.Source.Higham.Chapter27.Problem06`.
- Hygiene scan for `sorry`, `admit`, `axiom`, `unsafe`, and `opaque` - PASS (no matches).
- Representative `#print axioms` checks report only Mathlib's standard
  `propext`, `Classical.choice`, and `Quot.sound` axioms.

## Documentation

- Inventory: `docs/chapter27/CHAPTER27_SOURCE_INVENTORY.md`
- Not-proved ledger: `docs/chapter27/CHAPTER27_NOT_PROVED_LEDGER.md`
- Proof-source ledger: `docs/chapter27/CHAPTER27_PROOF_SOURCE_LEDGER.md`
