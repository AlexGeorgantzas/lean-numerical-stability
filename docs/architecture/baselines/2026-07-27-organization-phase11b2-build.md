# Organization Phase 11B2 build evidence (2026-07-27)

This record covers the bounded migration of the remaining 69 Chapter 6
constants from four historical algorithm/analysis modules into nine canonical
`Source.Higham.Chapter06` declaration leaves. Two declaration-free family
aggregates organize the former asides and block-antidiagonal results. The four
historical paths are now exact compatibility wrappers.

Development started from the pushed Phase 11B1 evidence revision
`aad584a2d50252860adcc38f0b7f5c92c738d2f2`. The immutable ownership map was
committed before implementation as
`c9a0513753122bb1fd171a7060fc5083a0550005`.

Candidate-worktree and clean-commit validation are recorded separately. The
implementation revision is
`fd8e5dbc8f7608751f8d82011ca52098dd3f6c63`. The architecture pair was
captured from that clean revision and committed as
`03814669f0b0c2998bed03cba3cbc674a75730d9`. This evidence update changes no
Lean declaration, proof, import, manifest, test, or captured measurement.

## Environment

| Item | Value |
| --- | --- |
| Platform | Windows 11 |
| Lean toolchain | leanprover/lean4:v4.29.0-rc3 |
| Mathlib revision | e8ea1afc32790ce1d4e1a4e45cc412ba9388716b |
| Production target | NumStability |
| Test driver | NumStabilityTest |

## Migration result

The four former owners were replaced by this canonical source hierarchy:

- `Source.Higham.Chapter06.Lemma06`, `Equation01`, and `Equation02` own the
  numbered lemma/equation surfaces;
- `Source.Higham.Chapter06.Asides` imports four focused aside leaves plus
  `Equation01` and the operator-two block result, reproducing the exact former
  `Higham6Asides` surface;
- `Source.Higham.Chapter06.BlockAntidiagonalNorm` imports the focused
  `OperatorTwo` and `InducedLp` leaves; and
- the declaration-free `Source.Higham.Chapter06` root now imports `Norms`,
  `Asides`, `BlockAntidiagonalNorm`, `Equation02`, and `Lemma06`.

The historical paths `Algorithms.Chapter06Lemma66`,
`Analysis.Higham6Asides`, `Analysis.Higham6BlockAntidiag`, and
`Analysis.HighamChapter6Duality` each import exactly one canonical target and
own no declarations. Production code imports no historical path. The two
direct Lemma 6.6 consumers now import `Source.Higham.Chapter06.Lemma06`, while
the `Algorithms` and `Analysis` entry points preserve their bounded former
surfaces through canonical imports.

Fifteen isolated one-import tests cover all nine declaration leaves, both
family aggregates, and all four old-only compatibility paths. Existing
Chapter 6, Algorithms, Analysis, Source, Higham, All, root, canonical-source,
and migration smokes were strengthened for the new organization.

## Exact compiled ownership and dependency preservation

| Canonical owner | Constants |
| --- | ---: |
| `Chapter06.Lemma06` | 20 |
| `Chapter06.Equation01` | 4 |
| `Chapter06.Equation02` | 3 |
| `Chapter06.Asides.EuclideanNormDifferentiability` | 2 |
| `Chapter06.Asides.UnitaryInvariance` | 6 |
| `Chapter06.Asides.ConditionNumberBounds` | 7 |
| `Chapter06.Asides.MaxNormInconsistency` | 6 |
| `Chapter06.BlockAntidiagonalNorm.OperatorTwo` | 3 |
| `Chapter06.BlockAntidiagonalNorm.InducedLp` | 18 |
| **Moved Chapter 6 source tail** | **69** |

The partition contains 56 public, ten generated/internal, and three private
constants: seven definitions and 62 theorems. The tracked manifest contains
69 rows and has file SHA-256
`33A67750AD55F9C1E856A3B8FF2868CF81EBE0E5144BF75EA992BB905E77E8FD`.
Its normalized inventory SHA-256 is
`28FDFD53016CDD5365ED32089DED59625F1E37007C119F9705B7F7C26B948581`.

The exact typed incident stream contains 440 edges: 158 signature and 282
body/proof edges. The 126-edge induced internal stream contains 37 signature
and 89 body/proof edges. Their frozen SHA-256 values are respectively
`9E879119F3FEB28FC64A6B554C59F110C685AFDB9C8BAE83D918709536950C28`
and
`880A472E8600F18DCA192C89FB7B3AF0A2157E395FB93426281646C4028C9987`.

The post-migration checker validates exact owner, logical name, kind,
visibility, multiplicity, private-name rewrites, structural imports, consumer
retargets, isolated tests, and the two-edge canonical owner DAG. It then
normalizes the nine destinations back to the four historical owners and
compares the complete Phase 11B1 and Phase 11B2 declaration/edge streams.

The normalized comparison reports zero missing and zero extra records. The
global graph remains exactly 81,950 declarations, 305,425 signature edges,
439,195 body/proof edges, and 491,557 union edges. The raw Phase 11B1 TSV has
SHA-256
`89A22BFBB70513DE4FEE3734AABC1FDADA3FC7C737164923808CBCD4FC79EB30`.
The clean Phase 11B2 TSV is 131,969,104 bytes with SHA-256
`AEBEAB80F4D98177960A830BB965F392DE2D9FD9463CDE7EFCACB7DE1570055E`.

## Candidate-worktree validation

| Command or gate | Result |
| --- | --- |
| Focused leaf, aggregate, wrapper, consumer, and import-test builds | passed |
| Targeted entry-point/import-smoke build | passed; 4,908 jobs |
| `lake build NumStability` | passed; 4,826 jobs |
| `lake test` | passed; 5,333 jobs |
| `lake build NumStability NumStabilityTest` | passed; 5,335 jobs |
| `lake env lean examples/LibraryLookup.lean` | passed |
| Nine-owner representative axiom audit | passed; exactly `propext`, `Classical.choice`, and `Quot.sound` |
| Phase 11B1 preservation checker | passed: 1,783 constants and frozen edge digests preserved |
| Exact normalized Phase 11B1/11B2 graph comparison | passed: 69 constants and the full graph preserved |
| Strict-source architecture capture and check | passed |

## Architecture baseline

| Measure | Result |
| --- | ---: |
| Lean modules | 1,035 |
| Source lines | 1,469,248 |
| Nonblank source lines | 1,402,798 |
| Direct imports | 4,152 |
| Internal import edges | 2,791 |
| External imports | 1,361 |
| Import cycles | 0 |
| Classified modules | 431 |
| Classification coverage | 41.643% |
| Unclassified modules | 604 |
| Aggregate modules | 87 |
| Compatibility modules | 108 |
| Reusable modules | 78 |
| Source modules | 151 |
| Internal modules | 2 |
| Upstream modules | 5 |
| Mixed modules | 0 |
| Modules missing module documentation | 217 |
| Historical naming exceptions | 399 |
| Uniquely owned declarations | 81,950 |
| Public declarations | 56,187 |
| Signature edges | 305,425 |
| Body/proof edges | 439,195 |
| Union edges | 491,557 |

The reviewed roles have zero direct or transitive reusable-to-source or
reusable-to-mixed paths. Classification is still incomplete, so the zero
mixed count is a ratchet over reviewed modules rather than a claim that the
604-module unclassified corpus is source-pure.

The `Algorithms` aggregate remains at 442 direct project imports. Its direct
`Analysis` imports fell from 45 to 43, while its direct `Source` imports rose
from 11 to 14. Compatibility now contains 108 wrappers with 208 direct
canonical targets. There are no unresolved imports, import cycles,
declaration-bearing umbrellas, or unsorted classified aggregates.

## Static validation

| Gate | Result |
| --- | --- |
| Layout, placeholder, test-reachability, and exact legacy-debt contract | passed: 1,035 modules |
| Classified source boundary | passed: zero forbidden direct or reachable paths |
| Compatibility contract | passed: 108 wrappers, 208 direct targets |
| Provenance contract | passed: 207 Apache files, five upstream modules |
| Aggregate structural and ordering contract | passed: 87 classified aggregates |
| Declaration-bearing umbrellas | passed: zero |
| Unsorted classified aggregates | passed: zero |
| Frozen Phase 11B2 pre-map check | passed: 69 constants, 440 incident edges |
| Post-migration ownership, owner-DAG, import, wrapper, and test contracts | passed |
| Baseline reproduction from the retained declaration TSV | passed |
| Independent production, test, map, and documentation review | passed after corrections |
| `git diff --check` | passed |

## Review corrections

Independent review confirmed the declaration partition, wrapper/aggregate
surfaces, consumer retargets, isolated tests, manifests, documentation counts,
and normalized full-graph comparison. It found stale present-tense references
to historical owners in the Chapter 6 coverage ledger and one consumer
docstring. Those references now distinguish former owners from current
canonical modules.

Review also found that the induced-`L^p` leaf's provenance header was a regular
comment while its only documentation comment was a section heading inside the
namespace. Lean requires imports to precede documentation commands, so the
final Mathlib-style layout is provenance comment, imports, titled module
docstring, then namespace. `Equation02` was normalized to the same pattern.
The Phase 11B2 checker now requires a module docstring before the namespace in
every one of the nine declaration-bearing leaves. Focused rebuilds and the
complete release gates passed after these corrections.

## Clean-commit verification

The production tree at implementation revision
`fd8e5dbc8f7608751f8d82011ca52098dd3f6c63` was clean before all release gates,
the declaration stream, and the architecture pair were regenerated. The
following checks were repeated from committed source:

| Command or gate | Result |
| --- | --- |
| Initial `git status --short` | passed: no output |
| Layout, compatibility, provenance, and frozen pre-map checks | passed |
| `lake build NumStability` | passed; 4,826 jobs |
| `lake test` | passed; 5,333 jobs |
| `lake build NumStability NumStabilityTest` | passed; 5,335 jobs |
| `lake env lean examples/LibraryLookup.lean` | passed |
| Representative axiom audit across all nine leaves | passed at the established ceiling |
| Fresh declaration/dependency extraction | passed: 131,969,104-byte TSV |
| Phase 11B1 preservation checker | passed |
| Exact normalized Phase 11B1/11B2 comparison | passed: zero missing and zero extra records |
| Clean strict-source capture and reproducibility check | passed |
| Named baseline capture from retained TSV | passed |
| Named baseline `--check` reproduction | passed |

The generated baseline records `library_source_clean: true`, implementation
revision `fd8e5dbc8f7608751f8d82011ca52098dd3f6c63`, and normalized source-tree
digest `46f1857e5b409e0ea98be74642b4feb8857e6792dfc2a0f6ce689ad422861534`.

## Captured artifacts

- [Human-readable architecture baseline](2026-07-27-organization-phase11b2.md)
- [Machine-readable architecture baseline](2026-07-27-organization-phase11b2.json)
- [Phase 11B2 immutable migration and ownership record](../migrations/2026-07-27-chapter06-source-tail-phase11b2.md)
- [Phase 11B2 declaration-ownership manifest](../declaration-ownership/chapter06-phase11b2.tsv)

The source, import, declaration, toolchain, Mathlib, ownership, axiom, and
documentation measurements were reproduced before this evidence-only commit.
