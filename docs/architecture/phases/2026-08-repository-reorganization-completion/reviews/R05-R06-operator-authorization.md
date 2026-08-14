# Temporary second-operator authorization for B0006/R05

Authority: `primary-human` (recorded by `claude-local` under the
primary-human planning delegation for the C0003 successor review).

The frozen phase scope assigns waves R05 and R06 to `codex-lane`. To run
the authorized R05+R06 pair in parallel with one operator per wave,
`claude-local` is temporarily authorized as a second `codex-lane` operator
**solely for B0006/R05**: planning-artifact stewardship, the B0006 worker
implementation in its activated named worktree, the B0006 delivery commit,
and pushes to exactly the `refs/heads/codex/reorg-completion-2026-08-r05-least-squares-underdetermined-ch20-ch21`
delivery ref. B0007/R06 remains exclusively `codex-local`.

Constraints, mirroring the accepted R12 (`codex-local`) and R03
(`claude-local`) expansions:

* the expansion is scoped to B0006 and confers no authority over B0007,
  integration, main pushes, checkpoint acceptance, or retirement;
* `claude-local` may not audit any B0006 artifact or delivery it authored;
  the independent audit passes to `codex-local` or `primary-human`;
* `codex-local` may not audit the planned/activation control commits
  authored by `claude-local` for its own wave-pair only insofar as it did
  not author them — the planned and activation controls for this pair are
  authored by `claude-local`, so their independent audit belongs to
  `codex-local` or `primary-human`;
* the authorization expires automatically at C0004 acceptance or when
  B0006 becomes terminal, whichever comes first, restoring `codex-lane`
  to its single `codex-local` operator.
