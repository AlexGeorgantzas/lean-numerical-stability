# Canonical module naming and layout

This document defines the target organization for NumStability. It applies to
new and touched canonical modules immediately. Historical compatibility modules
are listed in [`COMPATIBILITY.md`](COMPATIBILITY.md). Other pre-migration debt
is grandfathered only when named in
[`layout-exceptions.json`](layout-exceptions.json); the layout check requires
the exact reviewed set to be updated whenever debt decreases and rejects any
unreviewed addition.

## Organizing principle

The public filesystem describes mathematics, not the order in which a proof
was discovered.

```text
NumStability/
  FloatingPoint/
    Format/
    IEEE/
    Rounding/
  Analysis/
    Error/
    Conditioning/
    Perturbation/
    LinearAlgebra/
    Probability/
  Algorithms/
    Arithmetic/
      DotProduct/
      Summation/
    PolynomialEvaluation/
    LinearSystems/
      Triangular/
      LU/
      Cholesky/
      SymmetricIndefinite/
      QR/
      LeastSquares/
      Underdetermined/
      IterativeRefinement/
    MatrixEquations/
      Sylvester/
    MatrixFunctions/
    Transforms/
    RandomizedLinearAlgebra/
    TestMatrices/
  Source/
    Higham/
      Chapter01/
      ...
      Chapter28/
      CrossChapter/
  Upstream/
    Mathlib/
```

The tree is a target pattern, not a request to create empty directories. Add a
directory when migrated modules need it.

## Module roles

Each production module has exactly one primary role in
[`tiers.json`](tiers.json):

- `reusable`: source-independent definitions, algorithms, and theorems;
- `source`: results, aliases, examples, and discrepancies tied to a book or
  paper;
- `internal`: unsupported proof support owned by a nearby family;
- `upstream`: copied or adapted external code with preserved provenance;
- `aggregate`: a documented import-only entry point;
- `compatibility`: a documented import-only historical path;
- `mixed`: a temporary reviewed split queue, never a final role.

Reusable modules must not directly or transitively import source modules.

## Reusable names

1. Use UpperCamelCase Lean module components.
2. Name modules for mathematical concepts or algorithmic roles.
3. Do not use `Ch`, `Chapter`, `Higham`, `Problem`, theorem numbers, or other
   source locators in reusable paths.
4. Do not use proof-progress words in canonical public paths, including
   `Actual`, `Bridge`, `Closure`, `Endpoint`, `Operational`, `Prose`,
   `Remaining`, generic `Source`, `Support`, and `Whole`.
5. Use no underscores in canonical filenames.
6. Use the established acronym allowlist: `LU`, `QR`, `FFT`, `SVD`, `FMA`,
   `SPD`, `PSD`, `MGS`, and `LSQR`. Spell out project-local abbreviations unless
   this document is amended to standardize them.

When a banned word names a genuine mathematical concept, document the exception
in the module docstring and architecture review. Otherwise choose a semantic
name or place unsupported scaffolding in an `Internal/` directory below its
closest owner.

## Source names

Higham correspondence uses exactly this dialect:

```text
NumStability.Source.Higham.Chapter02.Problem10
NumStability.Source.Higham.Chapter08.Lemma08Discrepancy
NumStability.Source.Higham.Chapter10.Theorem07
NumStability.Source.Higham.Chapter13.Table01
```

- Use two-digit `ChapterNN` directories.
- Do not repeat the chapter number in a leaf filename.
- Use local zero-padded locators when the book has stable numbering.
- Spell out `Theorem`, `Lemma`, `Equation`, `Corollary`, `Problem`,
  `Algorithm`, `Example`, and `Table`.
- Do not create canonical `Ch`, `Thm`, `Eq`, `Cor`, or `Alg` abbreviations.
- `Correction`, `Counterexample`, and `Discrepancy` are permitted because they
  communicate mathematical or source status rather than proof progress.
- Put genuinely cross-chapter results in a named subgroup of `CrossChapter/`.

For a result with several independently useful stages, use a result directory
and an import-only result umbrella:

```text
Chapter19/Theorem06/Statement.lean
Chapter19/Theorem06/Elementwise.lean
Chapter19/Theorem06/ErrorBound.lean
Chapter19/Theorem06.lean
```

## Families and umbrellas

A single cohesive topic may remain a leaf file. Use a directory when a family
has multiple implementations, semantic stages, or independently useful
subtopics.

If `Foo.lean` and `Foo/` coexist, `Foo.lean` must:

- contain a module docstring explaining the family and its completeness
  contract;
- import supported canonical children with sorted, unique imports;
- contain no declarations;
- avoid compatibility and `Internal` imports unless its contract explicitly
  includes them.

Top-level entry points import family and chapter umbrellas plus genuine one-off
modules, not hundreds of implementation leaves. CI verifies advertised
reachability.

During the compatibility window, the historical `NumStability.Algorithms`
aggregate may retain explicitly ratcheted source imports needed to preserve its
old surface. This is an aggregate compatibility obligation, not permission for
reusable algorithm modules to depend on source correspondence.

Do not create `Basic`, `Defs`, `Lemmas`, or `Internal` modules merely for visual
symmetry. Every boundary needs a mathematical or dependency rationale.

## Documentation

Every canonical declaration-bearing module has a `/-! ... -/` module docstring
covering:

- its architectural role and mathematical scope;
- principal public declarations;
- important implementation boundaries;
- source citations when applicable.

Keep root community files conventional: `README.md`, `CONTRIBUTING.md`,
`LICENSE`, `CHANGELOG.md`, and `CITATION.cff`. Below `docs/`, use descriptive
lowercase paths, archive superseded dated audits, and avoid filenames named for
temporary tools or contributors.

## Compatibility

Old paths remain import-only wrappers until a declared breaking release. They
retain historical spelling and are not examples for new modules. A wrapper must
appear in the compatibility and tier manifests and have an isolated old-only
import test.

Declaration renames are separate API changes and are not performed merely
because a module moves.
