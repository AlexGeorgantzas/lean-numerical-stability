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

Through Phase 10C, reviewed source families cover the canonicalized Higham
frontiers in Chapters 1, 2, 4, 8, 10--14, 17, 20--27, and cross-chapter
locators. Exact `aggregate` rules identify every declaration-free chapter and
family umbrella; canonical leaves inherit `source` from the Source prefix and
historical owners use exact `compatibility` rules. Reusable extractions include
the floating-point operation laws, IEEE naive maximum, summation families,
triangular solves, fast-multiplication recurrences, probability analysis, and
the reviewed foundational leaves recorded in `tiers.json`.

The Phase 10C ratchet classifies 349 of 967 production modules: 130 as source,
67 as aggregate, 94 as compatibility, 51 as reusable, 2 as internal, and 5 as
upstream. The explicit unclassified queue is 618 modules and the mixed queue
remains empty. The `NumStability.Algorithms` direct-import ceilings are 444
imports below `NumStability`, including 10 below `NumStability.Source` and 45
below `NumStability.Analysis`.

Because structural aggregates do not themselves own declarations,
`reusable_entrypoints` separately lists aggregates whose entire reachable
surface must obey the reusable-to-source dependency gate. This keeps structural
role and dependency semantics distinct: `Core`, `FloatingPoint`, and
`FloatingPoint.IEEE` remain import-only aggregates while still seeding the
transitive forbidden-edge audit.
