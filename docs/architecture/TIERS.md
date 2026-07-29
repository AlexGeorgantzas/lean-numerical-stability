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

Through Phase 11B2, reviewed source families cover the canonicalized Higham
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
declarations. Phase 11B2 then assigned the 69 declarations from the four
separately audited Chapter 6 owners to nine canonical source leaves and added
the declaration-free `Chapter06.Asides` and
`Chapter06.BlockAntidiagonalNorm` family aggregates. Historical
`Algorithms.Chapter06Lemma66`, `Analysis.Higham6Asides`,
`Analysis.Higham6BlockAntidiag`, and `Analysis.HighamChapter6Duality` are exact
one-target compatibility wrappers.

Phase 12 completes the Block LU semantic split. The reusable
`Algorithms.LinearSystems.LU.BlockLU` aggregate exposes eleven reusable leaves,
including the final `RecursiveFactorization` owner and its two reviewed private
helpers. The source cutover moves the remaining 1,695 semantic declarations
into 66 new Chapter 13 leaves and the pinned `Equation25` and `Table01` shells;
the previously extracted `Theorem05.Recurrences` leaf makes the complete
`Source.Higham.Chapter13.BlockLU` contract an explicit 69-leaf aggregate.
Eleven declaration-free source family aggregates provide narrower discovery
surfaces without becoming declaration owners.

The historical `Algorithms.LU.BlockLU` module is now a declaration-free
two-target compatibility facade over the reusable and source aggregates. All
nine non-test direct consumers use the semantic owners they actually need, so
no declaration-bearing production module imports that facade. The private-name
normalization contract contains the two recursive-factorization identities and
the 17 source-owner identities required by `Theorem02.Factorization` and
`Theorem02.Uniqueness`.

The final Phase 12 source-cutover ratchet classifies 529 of 1,131 production
modules (46.773%): 218 as source, 103 as aggregate, 109 as compatibility, 92 as
reusable, 2 as internal, and 5 as upstream. The explicit unclassified queue is
602 modules, and no fully classified module is marked mixed. The
`NumStability.Algorithms` direct-import ceilings are 443 imports below
`NumStability`, including 43 below `NumStability.Analysis` and 15 below
`NumStability.Source`. The remaining layout debt is 216 missing module
docstrings and 399 noncanonical historical module names; the compatibility
inventory contains 109 wrappers with 210 direct targets.

Because structural aggregates do not themselves own declarations,
`reusable_entrypoints` separately lists aggregates whose entire reachable
surface must obey the reusable-to-source dependency gate. This keeps structural
role and dependency semantics distinct. The Phase 11B1 reusable seeds include
`Analysis.Norms.Core` and the `Analysis.Asymptotics`, `Conditioning`,
`LinearOperators`, `MatrixNorms`, `OperatorNorms`, `SingularValues`, and
`VectorNorms` family umbrellas. Existing reusable seeds such as `Core`,
`FloatingPoint`, `FloatingPoint.IEEE`, `Analysis.Equidistribution`, and
`Analysis.LeadingDigits` remain import-only aggregates while still seeding the
transitive forbidden-edge audit. Phase 12A additionally seeds
`Analysis.FirstOrder`, `Algorithms.LinearSystems`,
`Algorithms.LinearSystems.LU`, and `Algorithms.LinearSystems.LU.BlockLU` so
that no structural layer can hide a reusable-to-source path.
