# Temporary second-operator authorization for B0005/R03

Authorized at `2026-08-13T13:05:00-04:00` by `primary-human` against the exact
active-control commit `1166874cb986d09f357d092f1171a31d7f8b2332` and the
immutable C0002 worker base `9d2334d77f1a38f8a4caa81fe53eeb11a8e3e7cd`.

The immutable `codex-lane` assignment is preserved for R03. For this one wave,
`claude-local` is explicitly authorized as the lane's temporary second operator
solely for B0005/R03; `codex-local` remains an authorized operator and the
recorded planning/activation operator. This authorization does not permit
either operator to work another block, change the selector, projection, routes,
private map, test plan, or shared request, consume any other branch's
postimage, or broaden the B0005 scope. All 121 R0005 paths remain
integrator-only for both operators.

The grant was issued directly by the primary human operator to resolve the
delivery gap after activation-control CI (run `31697060516`, job
`94437144462`) went green with no worker execution begun. The activation
review `reviews/R03-activation.md` remains byte-immutable at its pinned
SHA-256 `752B79BC9BBB2B492FA50DD43EC7E108DEF60D24D72B4F602CF2055B29189DB2`;
its recorded `codex-local` planning/activation operator attribution is
historical fact and is not rewritten by this expansion.

Because `claude-local` performed the independent read-only audits of the R03
planned-control and activation-control packets, and now becomes an authoring
operator, the independent audit of any B0005 delivery produced by
`claude-local` passes to the primary-human directly or to `codex-local`;
`claude-local` may not audit its own delivery. The prior planned-control and
activation-control audit verdicts predate authorship and remain valid.

The authorization expires automatically when the next checkpoint after C0002
is recorded or when B0005 becomes terminal, whichever occurs first. At expiry
`claude-local` must be removed from the `codex-lane` operator set; the
expansion confers no continuing authority and cannot be reused by a later wave
without a fresh primary-human review. `B0005.operator_ids` retains both
operators as the historical record of authorized executors for this wave.
