# Executable tier inventory

[`tiers.json`](tiers.json) is the machine-readable classification used by the
architecture generator. Exact module rules take precedence over prefix rules.
The source audit reports classified import edges and treats every direct or
transitive path from `reusable` into `source` or `mixed` as forbidden. This
prevents aggregate, compatibility, internal, or not-yet-classified
intermediate modules from hiding a dependency inversion.

The inventory is intentionally partial during this migration. Large historical
areas below `Algorithms/` and `Analysis/` still mix reusable mathematics,
numbered-source correspondence, and proof support; assigning either directory
one blanket tier would hide the problem. The generated baseline therefore
reports both classification coverage and the complete unclassified queue.

A zero forbidden-edge count is conclusive only when classification coverage is
100% and no `mixed` modules remain. Until then, the physical-source-target gate
is not satisfied, even when all currently classified reusable modules have zero
source or mixed imports.

When a module is reviewed:

1. classify it by mathematical role, not pathname;
2. add the narrowest exact or prefix rule that does not misclassify siblings;
3. run the strict source audit;
4. resolve any new reusable-to-source edge or document why the proposed tier is
   wrong;
5. split mixed modules before claiming complete coverage.

`compatibility` is a transitional tier for old import-only paths, and
`aggregate` is used for umbrella entry points. Neither is a destination for new
mathematical declarations. `mixed` marks a reviewed module that still contains
more than one declaration tier; it is an explicit split queue, not a permanent
architecture category.

The Chapter 1 Section 1.17 migration uses exact `aggregate` rules for
`NumStability.Source.Higham.Chapter01` and its `Section17` child. The five
canonical leaves inherit `source` from the `NumStability.Source` prefix. The
six historical `NumStability.Analysis.NonrandomRounding*` paths use exact
`compatibility` rules; there is deliberately no source-tier prefix rule for
that historical directory.

Through Phase 11B1, reviewed source families cover the canonicalized Higham
frontiers in Chapters 1, 2, 4, 6, 8, 10--14, 17, 20--28, and cross-chapter
locators. Exact `aggregate` rules identify every declaration-free chapter and
family umbrella; canonical leaves inherit `source` from the Source prefix and
historical owners use exact `compatibility` rules. Reusable extractions include
the floating-point operation laws, IEEE naive maximum, AddCircle
equidistribution, decimal leading-digit analysis, summation families,
triangular solves, fast-multiplication recurrences, probability analysis, and
the reviewed foundational leaves recorded in `tiers.json`. Canonical Problem
2.11 owns only its source samples while re-exporting the reusable decimal,
empirical-histogram, and logarithmic-distribution APIs needed for its complete
source locator; the Section 2.7 power-frequency conclusion has a separate
source leaf. Phase 10E additionally assigns the Hyman determinant development
to Chapter 14 Problem 14.14, the attainment and nonattainment refinements to
Chapter 21 Theorem 21.3, and generic homogeneous-space measure uniqueness to
reusable Haar probability analysis. Phase 10F separates the generic
Weyl--Mirsky API into reusable singular-value analysis from its Chapter 14
Problem 14.15 source endpoint, assigns the row-wise backward-error measure to
Chapter 21 Theorem 21.4, and assigns the literal Hilbert determinant ratio
discrepancy to Chapter 28 equation (28.2).

Phase 11A extracted the literal ambient-radius realization of Higham's Theorem
6.4 into `NumStability.Source.Higham.Chapter06.Theorem04` and made the old
`NumStability.Analysis.Norms` path a two-target compatibility facade. Phase
11B1 then assigned every declaration from the residual Core owner to one of 20
reusable semantic leaves or four Chapter 6 Problem leaves. It added seven new
declaration-free aggregates and made `Analysis.Norms.Core` an eighth newly
classified aggregate. Core is therefore no longer unclassified and owns no
declarations. The separately audited `Algorithms.Chapter06Lemma66`,
`Analysis.Higham6Asides`, `Analysis.Higham6BlockAntidiag`, and
`Analysis.HighamChapter6Duality` owners remain explicitly unclassified until
Phase 11B2 relocates them.

The Phase 11B1 ratchet classifies 416 of 1,024 production modules (40.625%):
142 as source, 85 as aggregate, 104 as compatibility, 78 as reusable, 2 as
internal, and 5 as upstream. The explicit unclassified queue is 608 modules,
and no fully classified module is currently marked mixed. The
`NumStability.Algorithms` direct-import
ceilings are 442 imports below `NumStability`, including 11 below
`NumStability.Source` and 45 below `NumStability.Analysis`. The exact remaining
layout debt is 217 missing module docstrings and 403 noncanonical
historical module names; the compatibility inventory contains 104 wrappers
with 204 direct targets. The provenance contract remains 207 Apache-marked
files and five upstream modules.

Because structural aggregates do not themselves own declarations,
`reusable_entrypoints` separately lists aggregates whose entire reachable
surface must obey the reusable-to-source dependency gate. This keeps structural
role and dependency semantics distinct. The Phase 11B1 reusable seeds include
`Analysis.Norms.Core` and the `Analysis.Asymptotics`, `Conditioning`,
`LinearOperators`, `MatrixNorms`, `OperatorNorms`, `SingularValues`, and
`VectorNorms` family umbrellas. Existing reusable seeds such as `Core`,
`FloatingPoint`, `FloatingPoint.IEEE`, `Analysis.Equidistribution`, and
`Analysis.LeadingDigits` remain import-only aggregates while still seeding the
transitive forbidden-edge audit.
