# Shared-file requests

Workers do not edit integrator-owned manifests, root aggregates, tests, CI, or
phase checkpoints directly. The integrator creates one `Rxxxx.json` plus its
hash-pinned `Rxxxx.patch` here for every requested shared change. A request is
valid only through its target checkpoint and must become applied, rejected,
withdrawn, expired, or superseded when that checkpoint changes.

There are no active shared-file requests at checkpoint C0004. R0001 and R0002
are terminal applied records that retroactively register the exact, hash-pinned
integrator-owned deltas accepted at C0003 for W02 and at C0004 for W12,
respectively. Active branches B0004 and B0005 both begin with empty
`shared_request_ids`; any later shared request must be created and hash-pinned
by the integrator rather than edited into a worker branch.
