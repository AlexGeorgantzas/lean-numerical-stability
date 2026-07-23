# Summation-family migration

## Implemented canonical paths

`NumStability.Algorithms.Summation` remains the complete published family
entry point. The reviewed reusable leaves are:

- `Algorithms.Summation.Recursive.Core`;
- `Algorithms.Summation.Pairwise.Core`;
- `Algorithms.Summation.Tree.Core`;
- `Algorithms.Summation.Tree.Balanced`;
- `Algorithms.Summation.Tree.Chain`;
- `Algorithms.Summation.PlusMinus`;
- `Algorithms.Summation.DoublyCompensated`;
- `Algorithms.Summation.Accumulator`;
- `Analysis.Summation.Signs` and `Analysis.Summation.ErrorBounds`.

`Algorithms.Summation.Recursive` and `Algorithms.Summation.Pairwise` are
declaration-free family umbrellas. They deliberately combine their reusable
cores with the supported source leaves that their old single-file surfaces
exposed. Reusable production code imports `.Core`; broad discovery and existing
consumers may continue to import the family umbrellas.

The extracted Chapter 4 correspondence is canonical at:

- `Source.Higham.Chapter04.Problem03`;
- `Source.Higham.Chapter04.Section01.PairwiseSixTerm`;
- import-only `Source.Higham.Chapter04.Section01` and `Chapter04` umbrellas.

Every former root-level algorithm path remains an import-only compatibility
module. Production consumers use semantic canonical paths, and isolated tests
compile reusable, source, family, and historical surfaces independently.

## Dependency corrections

The original generic `SumTree` module imported recursive summation solely for
its chain-tree specialization. Its semantic layers are now:

- `Tree.Core` — tree structure, evaluation, and generic error theorems;
- `Tree.Balanced` — the balanced/pairwise specialization;
- `Tree.Chain` — chain trees and their equality with recursive summation.

The old proof-progress path `Tree.RecursiveBridge` is an import-only
compatibility shim to `Tree.Chain`. Generic and balanced tree consumers no
longer depend on the particular recursive algorithm. The historical `SumTree`
path and canonical `Tree` path remain complete umbrellas.

The dependency audit also established that `Accumulator`,
`DoublyCompensated`, `PlusMinus`, and `Analysis.Summation.ErrorBounds` have
source-independent APIs. Citations in their documentation record provenance;
they do not make the modules source correspondence. These modules are now
classified `reusable`.

After this batch the reviewed mixed queue is reduced from nine modules to two:
`Algorithms.Summation.Compensated` and `Algorithms.Summation.Insertion`.

## Module-system boundary

The family retains legacy `import` syntax. A probe confirmed that a file using
Lean's `module` / `public import` system cannot re-export the current legacy
dependency tree one wrapper at a time. Adopting modern visibility requires a
dependency-closed conversion in topological order and remains a separate
migration. Compatibility and API tests protect the current surface meanwhile.

## Deferred splits

Further slicing is deliberately dependency-driven:

- split `Analysis.Summation.ErrorBounds` into semantic conditioning and
  rounded-fold leaves when consumers justify the finer imports; its present API
  is already wholly reusable;
- split compensated summation at the generic FastTwoSum, Kahan, no-guard, and
  alternative-accumulation seams, extracting numbered Chapter 4 results and
  counterexamples to the source tree;
- extract the two concrete Higham insertion examples, then split insertion only
  where schedule, optimality, tree, and executor dependencies support it.

The current family umbrellas and compatibility shims remain stable throughout
those later batches.
