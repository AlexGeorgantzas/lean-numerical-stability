# I01 selection and overlap review

Status: planned packet materialized; independent semantic review is pending.

## Immutable bases and authority

- Accepted checkpoint: `C0007` at `4e26820d1f4989ec4ec77b7113085f593570e11b`.
- Planned-control parent: `8960f2a980be22166f321c4ba452eb547529b1fd`.
- Request: `R0014`, lane `integration-lane`, wave `I01`, milestone `M13`.
- Operator authorization: `C0007-M13-I01-CODE03-terminal-v2`, issued by
  `primary-human` to `codex-local` and terminating only after the exact leased V
  push, successful authenticated post-assurance V dispatch, and canonical
  local-ledger evidence recording, or earlier cancellation, drift, or
  revocation.
- This grant authorizes no R0014 or R0015 request resolution. Any later
  resolution is outside this grant and requires separate primary-human
  authority.
- The C0008-supported-API row is null, pending machine evidence only; it is not
  human review, checkpoint acceptance, request resolution, or authority for a
  C8 proposal, acceptance, status mutation, or finalization action.

The production/toolchain contents of all R0014 implementation paths at the
control parent match C0007. The request preimages therefore bind the immutable
C0007 checkpoint rather than mutable working-tree state.

## Twelve-row selection disposition

The selector `selectors/I01.tsv` accounts for every C0007 I01 inventory row.
Rows I01-01 through I01-05 and I01-07 through I01-12 are byte-identical no-ops:
their production write set is empty and each postimage SHA-256 equals its
preimage SHA-256. I01-06 is the only production change. It moves two declarations
without changing their names, namespaces, visibility, or normalized types into
`Counterexample.Inputs`; changes `Results` to import that leaf; and turns the
parent into an import-only aggregate over `Inputs` and `Results`.

The three production files in I01-06 are one indivisible rollback unit. A
partial application would duplicate declarations, leave `Results` unresolved,
or recreate the parent/child import cycle.

## Ownership and overlap disposition

- The parent is an exact I01 scope row and an exact live `phase.json.shared_paths`
  reservation.
- `Counterexample.Inputs` is an explicit exact shared-path extension owned only
  by this request.
- `Counterexample.Results` is the accepted R05 postimage at blob
  `27ac0065b39048678b2af0d023f457b63350e3b6`. R0014 is a sequential,
  import-only amendment rooted at that exact accepted blob; it does not reopen
  B0006/R05 or mutate accepted R05 evidence.
- `NumStabilityTest.lean`, the new I01 test subtree, `tiers.json`, and
  `layout-exceptions.json` are integrator-owned shared state reserved by R0014.
- No active worker branch or active request owns any R0014 implementation path.
- R0015/CODE03 has a disjoint two-path implementation boundary. It neither
  consumes nor reassigns R0014 paths.
- Historical delivered, accepted, retirement-due, or retired branches are not
  reused.

The exact changed-path ledger and the request patch contain the same sorted
twelve-path set. There is no ambiguous owner, overlapping live request, wrapper
removal, compatibility mapping change, or cross-packet rollback dependency.

## Test and API preservation boundary

The packet adds exactly six test files and preserves the existing R03
Results-only six-theorem test byte-for-byte. Isolated canonical, aggregate,
historical-only, PNorm.All, and Chapter17.Results.Series witnesses are enumerated
in `reviews/I01-test-plan.tsv`. The public declarations remain reachable through
the new child, the parent, the historical `Analysis.DoubleRounding` wrapper, and
the established broader entrypoints. No public declaration, namespace,
normalized type, visibility, compatibility wrapper, or supported import is
removed or renamed.

## Independent review boundary

`codex-local` generated the exact patch and evidence packet. It cannot serve as
the semantic reviewer for those artifacts. The registered non-service reviewer
is `primary-human`; selector and test-plan rows remain
`awaiting_independent_review` until that reviewer records an inspection of the
exact hashes. CI replay is additional verification and is not the semantic
reviewer.
