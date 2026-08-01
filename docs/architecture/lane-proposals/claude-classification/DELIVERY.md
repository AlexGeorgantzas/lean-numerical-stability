# Lane delivery report

> **Status: superseded delivery history.** The original reported implementation
> head `7044bf66f0572b079bfff61131d395dc9edc999e` was not merged as the
> production implementation and must not be cherry-picked. Its report history
> was retained through `10ec7ce5a3281fd6bbcbd4a673416500342d7621`;
> refreshed Chapter 9 and Chapter 11 implementations were integrated separately
> and both have `INTEGRATED_POST_PASS` status. No request or blocker below is
> current.

## Identity

- Lane: `classification-ch09-ch11`
- Engine/subscription: `Claude subscription 4`
- Repository/remote: `https://github.com/AlexGeorgantzas/lean-numerical-stability.git`
- Frozen base SHA: `6487fc33088523b8f27ecde9ad613515b78f9977`
- Coordinator-published evidence base: `6ecc4d5513226e67594bb22985913f6a4a383e5c`
- Branch: `codex/org-classification-prep`
- Final implementation HEAD (parent of report commit): `7044bf66f0572b079bfff61131d395dc9edc999e`

## Ordered commits

1. `3b1532d08eaedef4507f1f3569bc37bec269e235` — preserves and classifies the frozen 386-module queue with deterministic proposal tooling.
2. `b787ddd19ff9cbc22377166f03bf2ca37119d6cd` — adds the complete Chapter 9 format-2 preparation contract and checker.
3. `06a3e2400adff181838807a488ee00dba4943a9d` — adds the complete Chapter 11 contract, including explicit Chapter 9 dependencies.
4. `7044bf66f0572b079bfff61131d395dc9edc999e` — adds isolated smoke modules, validation evidence, and the integrator request.

## Scope

- Scope-check command/result: packet `check_scope.py` against evidence base `6ecc4d5513226e67594bb22985913f6a4a383e5c`; PASS, 4 commits inspected, 43 touched/new paths.
- Changed paths: 3 files below `NumStabilityTest/Worker/ClassificationAudit/`, 31 proposal/evidence files below `docs/architecture/lane-proposals/claude-classification/`, and 9 scripts below `tools/architecture/lane_claude_classification/`.
- Forbidden/shared paths changed: none.
- Production Lean paths changed: none.
- Integrator-only patch requests: add the three isolated worker imports to `NumStabilityTest.lean`, exactly as specified in `INTEGRATOR_REQUEST.md`.

## Semantic evidence

- Pristine source/blob/`.ilean` hashes: `ch09/frozen-owners.tsv` has all 11 owners; `ch11/frozen-owners.tsv` has all 66 owners. The acceptance files hash every contract artifact.
- Baseline declaration TSV: format 2, 56,898 declarations, 649,224 typed edges, 115,724,349 uncompressed bytes, SHA-256 `32ADA469E27A971E9B0BB972F29C51E1DCBE99104A1492D4C69549C339825563`; zip SHA-256 `1C2538B428B8EC3610B3C09BBB6A4CF23ECA9F0DB17EE4AE5B63E4F371AECDED`.
- Candidate declaration TSV: not created; this lane performs no production move and therefore has no honest post/stage candidate graph.
- Ownership/signature comparison: pre checks PASS for all 4,420 Chapter 9 declarations and all 6,385 Chapter 11 declarations, with exact kind/visibility preservation.
- Signature typed-edge comparison: frozen internal graph contains 8,784 Chapter 9 and 36,158 Chapter 11 signature edges; route and destination-DAG contracts validate in pre mode.
- Body/proof typed-edge comparison: frozen internal graph contains 15,114 Chapter 9 and 44,911 Chapter 11 body edges; route and destination-DAG contracts validate in pre mode.
- Reviewed private-owner normalization: 28 Chapter 9 and 146 Chapter 11 authored private roots, all explicitly listed in each `private-rewrites.tsv`.

## Classification proposal

- Frozen inventory: 386 rows, SHA-256 `C0B1C88F34461A44305D269C880F7581BDD7F1D9CC69CF9A144EA099C6A6DF54`.
- Exclusions: 217 rows, SHA-256 `8CCBFA4191741B37BD3DD5748079A7505AF008A515077A25BABE9E23825B73C8`.
- Partition: exact and disjoint; union is all 603 frozen unclassified modules.
- Proposal: 386 rows, SHA-256 `C86D0C7D7A192CCE4FABA449BDDA76F303DBB3765FEEEF85C027DA5F9EDADAD5`.
- Categories: 129 reusable, 212 source, 44 mixed pending split, 1 aggregate, 0 compatibility, 0 internal.
- Main drift refresh: exactly six queue blobs changed after the packet base; all six are recorded, including the three BlockLU import cutovers and the two added `StationaryIteration` declarations.

## Verification

- Ownership checker negative self-tests: PASS; cycle rejection, private rewriting, format validation, and unsafe shared-manifest output rejection exercised.
- Pre/stage/post ownership gates: Chapter 9 pre PASS; Chapter 11 pre PASS; stage/post correctly NOT RUN because no production migration exists.
- Canonical-only tests: proposed destinations do not yet exist and are checked statically; no build claimed.
- Isolated old-only tests: three required modules created; compilation deferred under the coordinator-owned Lean mutex.
- Focused leaf builds: NOT RUN by explicit coordinator instruction while main CI repair owns the shared build mutex.
- Downstream builds: NOT RUN for the same reason.
- Layout/compatibility/provenance/strict-source gates: compatibility PASS; provenance PASS; static trust-marker scan PASS; layout exits 1 solely for the three intentionally standalone worker modules and has an exact integrator patch request.
- `lake test`: NOT RUN by explicit coordinator instruction.
- `lake build NumStability NumStabilityTest`: NOT RUN by explicit coordinator instruction.
- Axiom probes: no new `sorry`, `admit`, top-level `axiom`, or top-level `constant` found statically; compiled axiom probes are not claimed.
- `git diff --check`: PASS.
- Final clean status before this report: clean.
- Full machine-readable command log: `VALIDATION.json`; concise interpretation: `VALIDATION.md`.

## Cross-lane notes

- Chapter 9 remains `BLOCKED_ON_BLOCKLU_INTEGRATION` until the integrator globally verifies the BlockLU checkpoint observed at `6ecc4d5513226e67594bb22985913f6a4a383e5c`.
- Chapter 11 remains `BLOCKED_ON_CH09_INTEGRATION`; its contract records 61 explicit Chapter 9 dependency rows. Chapter 9 and Chapter 11 must not be implemented in parallel.
- The packet's 386/217 inventory is frozen at `6487fc33088523b8f27ecde9ad613515b78f9977`; source/import refresh evidence is deliberately based on published main `6ecc4d5513226e67594bb22985913f6a4a383e5c`.
- No branch was pushed or merged. The parent integrator requested a local commit-only handoff and will decide publication.

## Integrator refresh at `9e7c8e324`

The original delivery evidence above remains the worker's historical record at
`6ecc4d551`. Before integration, the coordinator refreshed the usable proposal
against `9e7c8e32437d6ea28bf297fc4f08756288df9b26`:

- `HighamChapter8` and `MatrixInversion` now reflect the CI source-graph repair.
- The obsolete `MatrixInversion -> HighamChapter9` consumer row was removed.
- Ten obsolete Chapter 9 BlockLU umbrella imports were replaced by forty exact
  canonical imports; the contract now has 280 import rows and 28 downstream
  consumers.
- Chapter 9 pre-check passes with all 4,420 declaration routes unchanged.
- Chapter 11 pre-check passes with all 6,385 routes unchanged and remains
  blocked until Chapter 9 is integrated and its current imports are regenerated.
- Acceptance hashes were normalized to the repository's committed LF byte form;
  the worker's pre-commit Windows CRLF hashes were not reproducible in a clean
  checkout even though Git-normalized TSV content was identical.

Chapter 9 is no longer blocked on BlockLU: strict-source and the full local
library/test build passed at `9e7c8e324`. It remains ordered after QR solely to
serialize shared aggregate/manifest edits.
