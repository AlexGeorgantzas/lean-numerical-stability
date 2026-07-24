# Compensated-summation migration, phase 4A

Date: 2026-07-23

## Scope and rationale

This batch begins the staged split of
`NumStability.Algorithms.Summation.Compensated`, the final module classified as
`mixed` after organization Phase 3.  It extracts the reusable local
correction-formula and finite FastTwoSum layers and moves the self-contained
Higham Problem 4.10 / Priest six-term example into the canonical source
hierarchy.

The block is a one-way source island: it starts at the heading
`Higham Problem 4.10 / Priest six-term example` (pre-migration line 12,865),
ends with
`problem410PriestInput_t24_first_sum_ieeeSingle_rounds_to_67108864`
(pre-migration line 13,114), and is followed by the reusable lemma
`kahan_backward_error_forward_bound_core`.  No declaration outside the block
depends on the Problem 4.10 declarations.

Base revision: `312a970cddfb5c41da81237bb34b5cb5fd0c93e4`.

## Exact module map

| Previous owner | Canonical owner | Exact declaration range | Role |
| --- | --- | --- | --- |
| `Algorithms.Summation.Compensated` | `Algorithms.Summation.Compensated.CorrectionFormula` | `CorrectionFormulaTrace` through `correctionFormulaTrace_e`, inclusive (pre-migration lines 108–135) | reusable local correction trace root |
| `Algorithms.Summation.Compensated` | `Algorithms.Summation.Compensated.FastTwoSum` | `finiteCorrectionFormulaTrace` through `FastTwoSumFiniteCertificate.of_two_signed_sterbenz` (pre-migration lines 141–462), then `FastTwoSumFiniteCertificate.of_exact_add` through `finiteCorrectionFormulaTrace_exact_of_base2_abs_le` (pre-migration lines 631–1,610) | reusable finite round-to-even certificate and exactness API |
| `Algorithms.Summation.Compensated` | `Source.Higham.Chapter04.Problem10` | `problem49PriestInput` through `problem410PriestInput_t24_first_sum_ieeeSingle_rounds_to_67108864`, inclusive | Higham Problem 4.10 source correspondence and source-correct aliases |
| `Algorithms.Summation.Compensated` path | unchanged transitional complete-family import | imports `Source.Higham.Chapter04.Problem10` while later compensated layers are extracted | compatibility during the staged split |
| `Source.Higham.Chapter04` | unchanged aggregate | adds `Source.Higham.Chapter04.Problem10` | canonical Chapter 4 source entry point |

All declarations remain in namespace `NumStability`; no declaration is
renamed and no theorem statement or proof is changed.  The historical
`problem49...` names remain available beside the source-correct
`problem410...` aliases.

## Import and compatibility contract

- `Algorithms.Summation.Compensated.CorrectionFormula` imports only the
  floating-point model and is the reusable dependency root for later
  FastTwoSum and Kahan layers.
- `Algorithms.Summation.Compensated.FastTwoSum` imports the correction root
  and finite-format arithmetic; it does not import a source module or the
  complete compensated umbrella.
- The new source leaf imports only finite-format arithmetic and the tactic
  support needed by the existing proofs.
- `Algorithms.Summation.Compensated` imports the source leaf so its published
  surface remains unchanged during the staged migration.
- `Algorithms.CompensatedSum` remains an import-only historical wrapper over
  the complete compensated family.
- `Source.Higham.Chapter04` directly imports the new source leaf.
- Reusable consumers are not redirected through the source module.

## Isolated API checks

This batch adds direct reusable-leaf smoke modules for the correction trace
and FastTwoSum certificate API, plus a direct source-leaf smoke module that
checks both a historical
`problem49...` declaration and a canonical `problem410...` declaration.  The
existing Chapter 4 entry-point test gains a Problem 4.10 check, and the
old-only compensated compatibility test gains the same source declaration so
an unrelated import cannot hide a broken compatibility surface.

Validation requires:

1. isolated builds of `Algorithms.Summation.Compensated.CorrectionFormula`,
   `Algorithms.Summation.Compensated.FastTwoSum`, and
   `Source.Higham.Chapter04.Problem10`;
2. an isolated build of `Algorithms.Summation.Compensated`;
3. direct source, Chapter 4 aggregate, canonical compensated, and historical
   wrapper smoke tests;
4. declaration extraction/API-count comparison;
5. strict source-boundary, compatibility, provenance, layout, aggregate-order,
   and baseline reproducibility checks.

## Risks and deferred work

The main risk is accidentally importing the broad compensated umbrella from
the source leaf, which would create a cycle and conceal the intended source
boundary.  The source leaf therefore imports only lower-level prerequisites.

This batch does not claim that `Algorithms.Summation.Compensated` is reusable
or declaration-free.  Correction/FastTwoSum, Kahan core and coefficient
layers, finite-format/error-bound layers, no-guard variants, and remaining
Chapter 4 examples are mapped and migrated in subsequent Phase 4 batches.
