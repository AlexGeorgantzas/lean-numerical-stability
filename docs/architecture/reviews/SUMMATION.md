# Summation-family migration

## Implemented canonical paths

The reusable family now has a discoverable umbrella and semantic paths:

- `Algorithms.Summation.Recursive`
- `Algorithms.Summation.Pairwise`
- `Algorithms.Summation.Insertion`
- `Algorithms.Summation.Tree`
- `Algorithms.Summation.PlusMinus`
- `Algorithms.Summation.Compensated`
- `Algorithms.Summation.DoublyCompensated`
- `Algorithms.Summation.Accumulator`

Every former root-level algorithm path remains an import-only compatibility
module. Production consumers use the canonical paths, and
`NumStability.Algorithms.Summation` is the family entry point.

Previously transitive conceptual dependencies are now direct:

- compensated and insertion summation import `Analysis.Summation` explicitly;
- insertion imports the tree layer explicitly;
- consumers no longer obtain tree or recursive declarations accidentally
  through a sibling compatibility module.

## Tree dependency correction

The original generic `SumTree` module imported `RecursiveSum` solely for its
chain-tree specialization. It is now split into:

- `Tree.Core` — tree structure, evaluation, and generic error theorems;
- `Tree.Balanced` — the balanced/pairwise specialization;
- `Tree.RecursiveBridge` — chain trees and their equality with recursive
  summation.

Thus generic and balanced tree consumers no longer depend on the particular
recursive algorithm. The historical `SumTree` path and the canonical `Tree`
path both remain complete umbrellas.

All new layers, the eight canonical algorithms, representative downstream
consumers, and the historical wrappers compiled. Initial first-build timings
also confirmed that `Compensated` and `Insertion` are the family outliers; the
timings were collected alongside a disjoint Chapter 9 build and are not a
controlled benchmark.

## Module-system boundary

The family retains legacy `import` syntax in this migration. A probe confirmed
that a file using Lean's `module` / `public import` system cannot re-export the
current legacy dependency tree one wrapper at a time. Adopting modern
visibility therefore requires migrating a dependency-closed subgraph in
topological order; doing that here would combine the summation move with a much
larger module-system conversion. The compatibility and API tests protect the
current surface until that conversion is scheduled separately.

## Deferred internal splits

Further slicing is deliberately deferred to separate changes:

- split `Analysis.Summation` between conditioning/componentwise perturbation
  and rounded-fold error expansions;
- split compensated summation at its FastTwoSum, Kahan, no-guard,
  alternative-algorithm, and source-counterexample seams;
- split insertion summation into algorithm, schedule, optimality, tree bridge,
  executor, and Higham examples.

Those changes alter fine-grained APIs and proof dependencies. The current pilot
establishes stable canonical imports and compatibility tests before attempting
them.
