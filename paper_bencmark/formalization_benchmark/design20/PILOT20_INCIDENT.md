# Pilot 20 first-task infrastructure incident

Pilot 20's first scheduled pair, `FAB19-EQ3.5`, began on Titan at
`2026-09-23T09:20:04Z` under the frozen development schedule. Condition R0
produced one candidate. Its model turn completed (170.848 s, 255,576 reported
tokens), and the candidate passed Lean compilation and proof-integrity
validation. Before faithfulness auditing could start, the controller passed
`None` for `forbidden_feedback_identifiers` to `AuditController`, whose
constructor requires an iterable. The resulting `TypeError` closed the
formalizer session and left the pair and campaign in incident states. There
is **no faithfulness verdict and no eligible paired comparison** from this run.

The immutable incident artifacts remain at
`/hdd/alexgeorgantzas/highambench/pilot20-dev3-20260923-a/`. In particular,
R0 submission 01 hashes are:

| Artifact | SHA-256 |
|---|---|
| `Candidate.lean` | `11b731771450ff32211a2e875ff10aa28387bcb1e5a8c225f11c9ef582df1035` |
| `formalizer/turn.json` | `4b4b88fbd5e772de9f9535705c84094171a40c2abfb958ed864b4279ae257779` |
| `validation.json` | `4b6cdb40fa7f44f522316b9938e250905f2661a2bb95e56e3df2358d0cfd080e` |
| `pair-report.json` | `ebb3839106156189f45372c2dd53d63d8c6ecedeafd4492b6b286ba75efd1820` |

The incident repair only normalizes the open-snapshot *absence of a finite
declaration whitelist* to an empty iterable for the feedback-name filter. It
does not change the source packet, corpus, model, prompts, retrieval scope,
validator, auditor rubric, or condition resource envelope. A regression test
covers the null-list case. Because the original measured conversation was
closed mid-loop, the controller will **not** treat that candidate as a
completed result or silently re-run it within Pilot 20. A new campaign,
`pilot21-dev3-controller-nullfix`, will use a distinct output directory and
record the controller commit in its frozen input identity. Pilot 20 remains
reported as an infrastructure incident regardless of Pilot 21's outcome.
