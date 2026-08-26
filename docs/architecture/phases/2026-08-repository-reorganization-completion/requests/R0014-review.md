# R0014 planned-packet review record

Status: mechanically frozen and replayed; independent semantic review by
`primary-human` remains pending. Generator/operator: `codex-local`.

## Bound artifacts

| Artifact | SHA-256 |
| --- | --- |
| `requests/R0014.json` | `CDF9CD8B9E5D8A06F60CB769801A5AC891F4468E1435207060F77B50BE1C67CE` |
| `requests/R0014.patch` | `3AC31AFC44B697FF830E0CF393FF1725F18B49022ABCF81D83742220FCCB3A88` |
| `requests/R0014-postimages.tsv` | `42F4ED7EFE7C611DE214A0E6FE4ABADA11034632A9086952EADCD1A8AA33A1C9` |
| `selectors/I01.tsv` | `4F669961538A406AF235C8E02B038D039A072F510C60F3863EFD7E93D417536F` |
| `reviews/I01-test-plan.tsv` | `6A4FDD8A6D467896A32BB9FDB1B3AF6CFFCEEB6DC5E9D33E95D59C70C60B2879` |
| `reviews/I01-selection-overlap.md` | `5A0A4852AD84095CFBFC973ACF37E45C8C0AA5FB09D8E8728356CC30C1AF43A9` |
| `reviews/I01-changed-paths.tsv` | `32D0E95A1F3AC0230647B86C94E3AFF869546BDDEA62678657C93EF22233AFC4` |
| `reviews/C0007-bounded-epoch-operator-authorization.json` | `9BD67B6336BA9D2943552AA09D19F580EC4A8A9298E85BC846854A201CB15129` |

The authorization record identifies the controlling decision as
`C0007-M13-I01-CODE03-terminal-v2`, issued by `primary-human`. Its exact path
manifest includes every control and implementation artifact above. The request
is active at C0007 with an empty resolution; this grant authorizes no R0014 or
R0015 resolution. Any later resolution is outside it and requires separate
primary-human authority. Its only C0008-named path is the null, pending
C0008-supported-API machine-evidence row; that row conveys no human review,
checkpoint acceptance, request resolution, or C8 proposal, acceptance, status,
or finalization authority. Every `origin/main` mutation is also outside this
grant.

## Exact selector and test-plan contracts

`selectors/I01.tsv` has the exact header:

```text
row_id	module	path	preimage_blob_oid	preimage_sha256	current_tier	decision	production_write	postimage_paths	postimage_sha256s	supported_signature_witnesses	test_modules	reviewer_id	status
```

It contains the ordered IDs I01-01 through I01-12 exactly once. A mechanical
round-trip against C0007 verified every blob OID and uppercase SHA-256. For all
eleven `production_write=false` rows, `postimage_paths=path` and
`postimage_sha256s=preimage_sha256`. An in-memory negative fixture replaced
I01-03's no-op SHA with 64 zeroes; validation rejected exactly the mutated
I01-03 SHA. The completion checker must retain an equivalent negative self-test.

`reviews/I01-test-plan.tsv` has the exact header:

```text
test_id	row_ids	path	test_class	import_mode	imports	expected_checks	forbidden_imports	disposition	reviewer_id	status
```

It names exactly six new I01 test paths plus the byte-identical preserved R03
Results-only six-theorem test. Rows are sorted by path and bind import mode,
expected checks, forbidden imports, disposition, reviewer, and review state.

`reviews/I01-changed-paths.tsv` has the exact header:

```text
path	action	rollback_unit	preimage_blob_oid	preimage_sha256	postimage_blob_oid	postimage_sha256	rationale
```

Its twelve sorted paths equal both the request path set and the patch path set.

## Detached C0007 replay

The patch was generated from a detached worktree at exact checkpoint commit
`4e26820d1f4989ec4ec77b7113085f593570e11b`. A second clean detached worktree
at the same commit ran `git apply --check`, applied the frozen patch, compared
the actual changed-path set with `R0014-postimages.tsv`, and recomputed every
postimage SHA-256. Result: twelve paths exactly, all hashes matched.

`git diff --check` passed. The patch is a single rollback unit at request level;
within it the three Counterexample production paths are specifically tagged
`counterexample_split` and may not be partially applied.

## Candidate validation evidence

The detached candidate produced the following evidence:

- `lake build NumStability.Source.Higham.Chapter02.Problem09.DoubleRounding.Counterexample.Inputs`
  succeeded after building all dependencies.
- The combined focused build compiled `Counterexample.Inputs`, `Results`, the
  import-only parent, `Analysis.DoubleRounding`, the new Inputs-only test, the
  new parent-only test, the new historical-only test, and the preserved R03
  Results-only six-theorem test without error.
- The broader combined I01 target was intentionally stopped at 3443/3498 jobs
  to release shared build capacity. The isolated PNorm.All and
  Chapter17.Results.Series smoke-test leaves therefore remain deferred to the
  exact planned-control/implementation CI and VERIFY-01; no green result is
  claimed for those two leaves here.
- `python tools/architecture/check_layout.py` passed with 2,928 production Lean
  modules and zero unclassified, mixed, missing-docstring, naming-exception,
  declaration-bearing-umbrella, and unsorted-aggregate rows.
- `python tools/architecture/check_compatibility.py` passed with 712 forwarding
  modules, 2,364 canonical targets, and the two expected pre-CODE03 retained
  production-import exceptions.
- `python tools/architecture/check_provenance.py` passed with 137 Apache-marked
  production files and five evidenced upstream modules.

The planned-control commit and exact implementation head must still pass the
phase/completion checkers, the two deferred focused smoke tests, and full CI.
Application additionally requires the first live owner comment, contract-only
A, exact-head A CI, committed and exact-lease-pushed T, and a successful
authenticated exact-head `workflow_dispatch` T observation. R0014 remains
unresolved after terminal V; any later C0008 proposal/acceptance and request
resolution require a separately authorized post-V epoch.

## Semantic-review boundary

The mechanical replay and CI are not independent semantic review.
`codex-local` generated and performed this packet, so it is ineligible to
review the exact artifacts or actions. The registered reviewer is
`primary-human`; every selector/test-plan row remains
`awaiting_independent_review` until the exact bound hashes are inspected and a
review disposition is recorded. This pending state does not weaken the active
shared-path reservation, but it prevents production application under the
authorization's activation conditions.
