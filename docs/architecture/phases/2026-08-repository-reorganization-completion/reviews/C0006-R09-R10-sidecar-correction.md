# C0006 R09/R10 branch-sidecar correction

Primary-human authorized correction of the branch sidecars landed by the
R09/R10 planned control `b12c9c6b829f9cf80a9ad6cf2d0c55f3530cd0d7`. It
changes no wave content, no route decision and no scope: only the recorded
evidence artifacts and their orderings.

## What the planned control landed

B0010, the immediately preceding wave, carries 22 sidecars.
B0011 carried 4 before this
correction. Two independent defects:

1. **Reduced schemas.** `declaration-routes` was 5 columns against B0010's 9,
   omitting `projection_order`, `source_ordinal`, `route_class` and
   `normalization_decision`. `route_class` is load-bearing:
   `check_completion_phase.py` validates it against
   `{relocate_whole, relocate_split}`, and on a 5-column table that read
   returns the empty string. `destination-dag` and `wrapper-imports` are also
   reduced; they are not corrected here (see the retained gap below).

2. **Missing ledgers.** `private-closure`, `post-move-import-manifest` and
   `test-plan` were absent entirely. All three are among the five ledgers a
   wave delivery must carry as byte copies of the control, so the delivery
   package could not be built.

Neither defect failed CI, because the pinned planned-control path set
encoded exactly the artifacts that were landed rather than the artifacts the
precedent requires.

## Corrected artifacts

| artifact | columns | rows | sha256 |
| --- | --- | --- | --- |
| `B0011-declaration-routes.tsv` | 9 | 570 | `63595D7E02294600F489C5338E73F5AF4A130C1ACE7A579A010F19B2CC3CF166` |
| `B0011-private-closure.tsv` | 11 | 423 | `1F342B033D9B8CECDDC75B77E3845F60EB89A96A5F86699C3D660F22A7CB4BC3` |
| `B0011-post-move-import-manifest.tsv` | 5 | 1,687 | `7C3163B5B004E5B1C7E1467F4DAFDEE95871CBA1EDE90BF7F5C0CCD3B8381632` |
| `B0011-test-plan.tsv` | 6 | 115 | `986C78B85FF59D90EAA5EB5CD3DD4D99776F1D9B9E47F623F33235A098B2939D` |
| `B0012-declaration-routes.tsv` | 9 | 225 | `0A63EF69BE9541DC6F1B413E39AEDD7D56144E189F7616588A3E4A5DC5319E9E` |
| `B0012-private-closure.tsv` | 11 | 225 | `0075F712627B5614238C9C8679F2B235A0D96E147A47BA314DB92AC122CA376C` |
| `B0012-post-move-import-manifest.tsv` | 5 | 1,204 | `79FFBAD0B43F934135863898DFE909838AC018AC2EB293C98BCB9D927EE8BBDD` |
| `B0012-test-plan.tsv` | 6 | 38 | `F51EF755334C279F485C8B23EB4F8FAE8E30CC77D5F42C55466A4388D8DB03B4` |

Every column header is byte-identical to its B0010 counterpart.

## Orderings, as measured from B0010

Each row order was measured against the precedent rather than assumed, after
an initial derivation that used a different convention throughout.

- `declaration-routes`: `(baseline_owner_module, projection_order)`, the order
  `check_completion_phase.py` describes as "sorted by owner and frozen
  baseline order". B0010 also satisfies the plain full-tuple order and
  `(owner, declaration)`, but only because its data never lets declaration
  name and projection order disagree; the owner/projection key is the one
  that stays correct when they do.
- `private-closure`: the full row tuple, case-sensitive, read as strings.
  B0010's apparent grouping by `closure_role` is an artifact of
  `NumStability.*` sorting before `_private.*`, not a rule.
- `test-plan`: `(test_class, target)`. The structural build order only looks
  sorted while no auxiliary test class is present.
- `private-normalization`: plain case-sensitive `sorted()`, required by
  `check_completion_phase.py` ("private map must exactly cover projected
  private names in sorted order").

## Deliberately not changed

`private-normalization` is **not** touched. Both committed files were already
correct: the generator's first derivation ordered them casefold, which both
the checker and B0010 contradict. The corrected generator now reproduces both
committed files byte-for-byte, which is the evidence that the committed
artifacts were right and the derivation was wrong.

| retained artifact | sha256 |
| --- | --- |
| `B0011-private-normalization.tsv` | `F9F5A7B2728E8583DD9106F0642B8DF6613235E5228DE5EB9A841B2FD3B328D6` |
| `B0012-private-normalization.tsv` | `8C32212542D49640263214B7816863CCEF44279E3B0CF98A71D7F7D994F6238C` |

## Retained gap

B0010 carries 22 sidecars; after this correction B0011 carries
8. The remaining difference is not addressed here and is recorded
so it is not mistaken for parity. Absent from both B0011 and B0012:

- `R0011-import-manifest.tsv`
- `branch-prefixes.txt`
- `consumers.tsv`
- `destination-modules.txt`
- `destination-prefixes.txt`
- `destinations.tsv`
- `external-owner-supply.tsv`
- `inventory.tsv`
- `module-routes.tsv`
- `overlap-review.json`
- `scope-rules.tsv`
- `shared-request-paths.txt`
- `source-commands.tsv`
- `test-modules.txt`
- `tier-assignments.tsv`

Also still reduced relative to B0010, and not corrected here:
`destination-dag` (3 columns against 4, dropping `signature_edges` and
`body_edges`) and `wrapper-imports` (2 against 6, dropping `base_blob_oid`
and the preserved/appended/post import breakdown).

Correcting those is a separate decision: none of them blocks the delivery
packages, and widening this correction to full B0010 parity would change
roughly forty artifacts rather than eight.

