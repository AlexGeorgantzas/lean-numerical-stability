# C0006 destination-rule contract amendment

The primary-human amends the phase contract so that a branch record's
`destination_prefixes` may contain `exact` rules in addition to `prefix` rules, and
requires that every `exact` destination name a path that is ABSENT at the branch's
`base_sha`.

## Why

`destination_prefixes` previously admitted prefix rules only, and every prefix had to be
vacant with respect to all other immutable scope rows. A wave that adds one new canonical
leaf to an existing directory therefore had to claim the entire directory, and was then
forbidden from doing so because the directory already held an `already_complete` module.
Those two rules together make "add a new canonical leaf beside its already-complete
siblings" inexpressible, which is precisely the layout this phase is driving toward.

All 82 conflicts raised for R09/R10 are with `already_complete` scope rows. Those rows carry
`-` for both `wave_id` and `lane_id`, so no branch owns them and the branch-versus-branch
collision the vacancy rule exists to prevent cannot arise from them. `owned_paths` cannot
carry the destinations either: it must equal every and only the wave's immutable scope paths.

## Why this is safe

An `exact` destination authorizes exactly one path, which is strictly narrower authority
than any prefix rule. The base-absence guard means such a rule can only ever authorize
CREATING a new file, never claiming an existing one. All four pre-existing overlap checks
(owned paths, integrator-owned shared paths, forbidden paths, and other immutable scope
rows) continue to apply to every destination rule regardless of match kind.

The amendment is backward-compatible: prefix-only records, including B0010 and every earlier
branch, satisfy the amended contract unchanged and are not revalidated differently.

## Scope

This amendment grants no new write authority over any existing file, no shared-path
authority, no integration or main-push authority, and no checkpoint acceptance or retirement
authority. Those remain with `primary-human`.
