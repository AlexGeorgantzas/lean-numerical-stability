# R03 route amendment: fanIn7 private-closure repair

Authorized at `2026-08-13T15:05:00-04:00` by `primary-human` against the exact
authority-control commit `c4f66cbdfdce6cf64d484be13290e7d2e60547f5` and the immutable
C0002 worker base `9d2334d77f1a38f8a4caa81fe53eeb11a8e3e7cd`.

## The defect

`NumStability.Algorithms.HighamChapters1To9SourceClosure` holds exactly three
declarations:

| declaration | visibility | frozen destination |
| --- | --- | --- |
| `higham8_18_fanIn7AbsApply_nonneg` | private | `…Chapter08.Equation18.FanInExecutor.FirstOrderForwardError` |
| `higham8_18_fanIn7Executor_family_firstOrder` | public | `…Equation18.FanInExecutor.FirstOrderForwardError` |
| `higham8_15_fanIn7Executor_residual_family_firstOrder` | public | `…Equation15.FanInExecutor.FirstOrderResidual` |

The private lemma is used by **both** public theorems (worker-base source lines 93 and
128). A Lean private declaration is module-scoped, so the frozen route — which places
the private and one user in the Equation18 destination but the second user in the
Equation15 destination — cannot compile under any implementation. Duplicating the
private would break the exact P0005 incident-edge replay (the second user's body edge
must normalize to the Equation18 private name), and inlining its proof would change the
frozen edge set. The contract was therefore internally unsatisfiable as reviewed; the
build failure `FirstOrderResidual.lean: Unknown identifier higham8_18_fanIn7AbsApply_nonneg`
is the mechanical witness.

## The amendment

Exactly one cell of `branches/B0005-declaration-routes.tsv` changes:
`higham8_15_fanIn7Executor_residual_family_firstOrder` now routes to
`NumStability.Source.Higham.Chapter08.Equation18.FanInExecutor.FirstOrderForwardError`,
restoring dependency-component closure (private plus both users in one module). Name,
visibility, kind, signature, proof and every typed edge remain untouched; the P0005
projection and the 398-row private map are unchanged (the checker permits any
allowed-prefix owner, and the private's pinned destination owner was already the
Equation18 module).

`…Equation15.FanInExecutor.FirstOrderResidual` consequently receives no declaration
from this owner and is delivered as a documented declaration-free bridge module that
imports the Equation18 destination, so the frozen R0005 consumer postimages — which
import both destination modules — and the frozen 48-target canonical test plan keep
resolving unchanged.

The validator's cascade ratchets require two consequential rows to change with the
route cell: `branches/B0005-module-routes.tsv` row for the owner now lists the single
Equation18 destination with the indivisible-component rationale, and
`branches/B0005-test-plan.tsv` drops the Equation15 canonical-only row (47 canonical
targets remain; the Equation15 bridge module is still compiled transitively by the
old-only wrapper test, the aggregate, and every frozen consumer postimage that imports
it). No selector, projection, private-map, private-closure, request, or consumer row is
modified. All three amended artifact hashes are re-pinned in
`tools/architecture/check_completion_phase.py` and `branches/B0005.json` in the same
control commit, which requires its own green Lean CI before the worker delivery may be
committed.
