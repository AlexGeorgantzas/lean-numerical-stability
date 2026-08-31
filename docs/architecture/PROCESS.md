# Architecture process

This document records how repository-wide architecture work lands on `main`
after the 2026-08 reorganization-completion phase. It replaces the bounded
P/A/T/I/V lifecycle, retired 2026-08-30 by the primary human's recorded
cutover decision after its second activation candidate failed CI on
environment divergence unrelated to repository content. The bounded branch
`codex/reorg-closeout-2026-08-m13-i01` remains immutable history at
`46c42a339b59a08cec3cbc439a929c3707447229`; the reviewed R0014/R0015
implementation it carried landed on `main` as
`9fbb1e36bcc85f866893e902cbe206ba468a65b0`.

## Gates

CI runs on every push to `main` and on every pull request
(`.github/workflows/lean_action_ci.yml`): the Python tooling compile pass,
the four checker self-tests, `check_phase.py --all-phases`,
`check_completion_phase.py`, `check_layout.py`, `check_compatibility.py`,
`check_provenance.py`, `generate_baseline.py --skip-declarations
--strict-source`, `lake build NumStability NumStabilityTest`, the literal
`lake test` test-driver step, and `check_warnings.py --check` against
`docs/architecture/warnings.json`.

Before every push, the same sequence runs locally, plus `lake test`.

The warning contract is a ratchet in both directions. `warnings.json` is the
authoritative census of every enabled diagnostic and every reviewed
`set_option linter.* false` suppression; the checker fails on a new
fingerprint, an exceeded global, per-kind, per-role, or per-file ceiling, a
warning in a file with no reviewed allowance, an unlisted or expired
suppression, or a toolchain, Mathlib, or platform change that invalidates the
capture. A diagnostic that stops firing also fails, as an improvement that
requires a reviewed baseline reduction: `--write-baseline` is review-only, so
the census can only fall through a reviewed batch, never drift.
A change that touches CI-facing tooling is additionally rehearsed in a
checkout-shaped local clone (long paths on, `core.autocrlf` off, detached
HEAD at the exact candidate commit) before it is pushed.

## Review model

- One dependency-contained batch per commit series, on a work branch.
- The primary human approves each batch in plain language (in session or by
  ordinary PR review); the approval sentence is recorded verbatim in the
  untracked evidence ledger.
- `main` moves only by fast-forward of a gated work branch after CI is green
  on the exact candidate commit.

## What the completion checker validates from here

The completion checker validates the immutable past epochs (C0000 through
C0007 and the recorded request history) exactly as committed, reading
historical postimages from pinned trees rather than freezing live bytes.
A batch that changes previously governed files needs no checker amendment
unless it changes the recorded history itself, which no batch may do.

## Non-goals (unchanged from the reorganization plan)

- No mass renames; wrappers preserved; declaration and namespace
  preservation; no speculative import churn.
- No second physical Lake library without benchmark evidence and a separate
  approved packaging decision.
- Declaration/API renames are never combined with path migration.
