# B0008/R04 implementation-operator redesignation amendment

Authority: `primary-human` (branch `owner_id` for B0008 and B0009).
Independent audit: `primary-human`. `claude-local` drafted this amendment and is
its beneficiary, so it must not be the sole reviewer.

## Defect

`docs/architecture/phases/2026-08-repository-reorganization-completion/reviews/R04-R08-activation.md`
(SHA-256 `1F4D2B8B585C9D8D919F5CCBA71FD6AB748D0D4CA859B65E133B51048ACE72FB`)
records, for `B0008` / wave `R04`:

| field | recorded value |
| --- | --- |
| Assignment | `Codex` |
| Lane | `claude-lane` |
| Recorded operators | `["claude-local", "codex-local"]` |
| Implementation operator after activation CI | `codex-local` |

The `codex-local` operator is unavailable. B0008 therefore cannot be delivered
as recorded: any delivery authored by `claude-local` would contradict
hash-pinned activation evidence naming a different implementation operator.

## Applied (2026-08-19, authorized by primary-human)

The owner instructed application of this amendment. The single-field change
below is applied to the activation review, and every pin of that file is
updated in the same control commit.

## Change

Exactly one field changes:

* B0008 implementation operator after activation CI: `codex-local` -> `claude-local`.

Everything else is unchanged and is deliberately restated so the amendment is
verifiable in isolation:

* `lane_id` stays `claude-lane` (already the recorded lane for both branches);
* `owner_id` stays `primary-human`;
* `operator_ids` stays `["claude-local", "codex-local"]` — `claude-local` is
  already a recorded operator on B0008, so no operator is added;
* the historical planning `Assignment` cell stays `Codex` as a point-in-time
  record;
* B0009/R08 is untouched (`Claude exclusively`, operator `claude-local`);
* no route, owner, selector, destination, projection, request, test, or
  production content changes;
* the frozen B0008 packet and all 3 pins quoted in the R04 activation prompt
  remain valid and were re-verified at control HEAD:
  * `B0008-declaration-routes.tsv`
    `122E11842F40D823FE003C7000528FCDF0E8A94658F411649BC411B066ECA314`
  * `B0008-private-normalization.tsv`
    `2349DFA9F94EEB183359B57A870E8F2CC5068662FB69EC4799FE7D99914858C1`
  * `B0008-post-move-import-manifest.tsv`
    `8BF709213AD10F47011BF4A2084A6E6B0D3E551C84FD8E7EFA8F43296EC50A86`

## Re-pinning required

`reviews/R04-R08-activation.md` changes, so its SHA-256 changes. Every pin of
that file is updated in the same control commit: the `refresh.evidence` entries
in `branches/B0008.json` and `branches/B0009.json`, the
`C0005_ACTIVATION_REVIEW_SHA256` constant and the B0008
`implementation_operator` fact in `tools/architecture/check_completion_phase.py`,
and the two `active_record_sha256` pins for the re-hashed branch records.

## Supporting finding (no action required)

The frozen B0008 post-move import manifest was independently checked for
elaboration sufficiency at C0004 by the declaration-graph test: for each of the
31 produced destinations, every module supplying a declaration referenced by
that destination's routed declarations is transitively reachable from the
destination's frozen imports, after routing R04-owned declarations to their own
destinations.

Result: **0 of 31 destinations have unreachable dependencies; 0 unresolved
dependency edges.** Cross-checks reproduce the R04 specification exactly — 31
produced destinations, 252 relocated declarations, 37 `retain_document` rows,
1,616 manifest rows. The B0008 manifest carries a per-line `provenance` column
and needs no amendment.

This is the opposite of the B0009/R08 manifest, which was derived from
declaration-graph edges alone and required the reviewed Variant A import
amendment (29 additions). No R04 equivalent is needed.

## Scope note

This amendment authorizes only who implements B0008. It does not merge, update
`main` beyond recording this control change, apply the R0009/R0010 union, create
C0005, accept a wave, or alter any worker delivery.
