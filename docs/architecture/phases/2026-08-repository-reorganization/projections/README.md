# Lane baseline projections

Each live branch references one active projection tied to the current accepted
checkpoint's combined format-2 baseline. A projection freezes the exact
historical declarations and typed edges selected for that wave, together with
its checker and expected counts. It is superseded whenever the checkpoint or
selected ownership contract changes.

No branch is activated in the origin-control commit. The W01 projection is
published with the first post-contract checkpoint.
