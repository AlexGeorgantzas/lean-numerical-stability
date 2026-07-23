# Reusable summation-sign API extraction

## Scope

The strict source-layer gate identified a reusable-to-mixed path from the
summation-tree framework into `NumStability.Analysis.Summation`. The tree code
used only the generic one-signed finite-family definitions and absolute-value
identities at the top of that file.

The exact role map is:

| Before | After | Role |
| --- | --- | --- |
| generic sign declarations in `NumStability.Analysis.Summation` | `NumStability.Analysis.Summation.Signs` | reusable |
| remaining declarations in `NumStability.Analysis.Summation` | `NumStability.Analysis.Summation.ErrorBounds` | mixed |
| original `NumStability.Analysis.Summation` path | imports both leaves | aggregate |

Declaration names and signatures are unchanged, so existing imports continue
to expose the same API.

## Dependency changes

The reusable tree core now imports `Summation.Signs` directly. The insertion
and pairwise summation modules and `Analysis.HighamChapter7` also use the
narrower leaf because their dependency intersection is limited to that API.
Compensated summation deliberately imports `Summation.ErrorBounds`: it also
uses the residual-distribution lemmas that remain there. Other implementation
consumers of those bounds use the same semantic leaf, while the top-level
analysis aggregate imports the family umbrella. Source-specific condition
numbers, numbered Higham problems, and floating-point summation-error theorems
remain in the mixed `NumStability.Analysis.Summation.ErrorBounds` module.

## Test and gate

An isolated smoke test imports only the new reusable leaf and checks its core
definition and equality characterization. A second test imports the umbrella
and checks both reusable and mixed declarations, preserving its historical
surface. The final strict-source graph gate reported zero reusable-to-source
and reusable-to-mixed reachable pairs. That zero is a reviewed-boundary result, not
a claim of complete separation while tier coverage remains 15.544%.

## Evidence

- Starting revision: `11a5241c7496851a8653080f30d39182c4eeb4d4`.
- Final targeted, full-suite, and strict-source evidence is recorded in
  [`2026-07-22-organization.md`](2026-07-22-organization.md).
