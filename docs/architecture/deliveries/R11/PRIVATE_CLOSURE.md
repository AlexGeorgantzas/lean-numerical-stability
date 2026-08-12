# R11 private normalization and reverse closure

`PRIVATE_NORMALIZATION.tsv` and `PRIVATE_CLOSURE.tsv` are byte-for-byte copies of the
authority files `branches/B0003-private-normalization.tsv` (SHA-256
`12E4D4F517D3678DABA4A11F57D36E22EE4428BC3598D3CA0FC7E41A9323E70E`) and
`branches/B0003-private-closure.tsv` (SHA-256
`74FA741BC9C9CCF802ED9999D64DB81E40F4D027A25351CAFF78F67196822145`). They are copied
rather than regenerated so the delivery cannot disagree with the contract it claims to
satisfy.

## Why private names change at all

Lean mangles a private declaration to `_private.<defining module>.<n>.<name>`. The
defining module is *inside the name*, so relocating a private declaration renames it.

That is the opposite of the rule an earlier floating-point wave had to adopt, where
private declarations could not move at all. The difference is P0003: it carries a
hash-pinned `--private-map` that is total over all 17 selected private declarations and
also pins each normalized declaration's destination owner. Because the rename is
declared in advance and checked, relocation is permitted here.

## The exact 17 rows

| destination | rows | kind |
| --- | ---: | --- |
| `…QR.Householder.PanelApplication` | 12 | module-prefix rewrite |
| `…QR.Householder.StoredQR` | 2 | module-prefix rewrite |
| `…Chapter19.Sensitivity.Bounds.Results` | 2 | module-prefix rewrite |
| `NumStability.Source.Higham.Chapter19.Core` | 1 | exact identity (retained outlier) |

16 rewrites plus one identity. Each rewrite changes only the module prefix: the logical
declaration name after the numeric private component is unchanged, and the numeric
component stays `0`. `CHECK_STATIC.py` and the focused tests both enforce that; the
delivery contains no private rename beyond these rows and no visibility change.

## Reverse closure: 954 declarations

The full typed reverse-dependent closure from the 17 seeds:

| slice | count |
| --- | ---: |
| private seeds | 17 |
| public reverse dependents | 937 |
| **total** | **954** |
| in selected owners | 280 |
| in protected non-owned owners | 674 |

The 674 in protected owners are the reason this closure is recorded rather than merely
counted. Those declarations are not edited by R11, but they consume the relocated
privates transitively, so a private rename that was not declared in the map would break
them. 129 of their owning modules are exactly the protected consumers in the R11 test
matrix, each compiled as an isolated target.

## How the normalization is verified

Three independent checks, none of which subsumes the others:

1. **Projection replay.** `check_completion_phase_projection.py` is given the pinned map
   and compares every declaration name, kind, visibility and typed incident edge against
   P0003. A private name that moved without a matching map row appears as a missing
   declaration together with every one of its incident edges. The C0001 preimage replay
   recorded in `reviews/R11-R12-projection-replay.md` deliberately omitted the map,
   because before delivery the private names are still the projection names; at delivery
   the map must be supplied.

2. **Focused Lean tests.** Each focused test rebuilds the mangled `Lean.Name` explicitly
   — string components, then the numeric component via `Name.num`, then the logical name
   — and requires the post-delivery name to be **present** and the pre-delivery name to be
   **absent**. Requiring the absence is what makes it a normalization test rather than an
   existence test. Building the numeric component with `Name.num` rather than parsing it
   out of a string is the correction R01 recorded after its first attempt failed.

3. **Static audit.** `CHECK_STATIC.py` requires each relocated body to be byte-identical
   to its C0001 preimage, which is what guarantees the private *declarations* themselves
   were moved rather than rewritten.
