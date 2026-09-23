# Pilot 21 first-review decision

The incident-successor Pilot 21 campaign at
`/hdd/alexgeorgantzas/highambench/pilot21-dev3-controller-nullfix-20260923-a/`
is frozen in `PAUSED_FIRST_REVIEW` after its first pair, `FAB19-EQ3.5`.
The pair is `AUDITED_PAIR_INELIGIBLE`; **there is no scored L/N effect**.
The campaign record SHA-256 is
`b5fb819ec447f2d6f37898b1ea47b8b68614c725d13a75f8de604f2994cfd58f`,
and the pair report SHA-256 is
`a6049aef65c4bd1da03afa697c9f422faf7ef68766df4c36e0d5082e4f884369`.

| First-submission diagnostic | N/R0 | L/R1 |
|---|---:|---:|
| Result status | `RETRIEVAL_INTERFACE_RULE_VIOLATION` | `ACCEPTED_FAITHFUL` |
| Contestant active seconds | 231.801 | 213.335 |
| Retrieval seconds | 13.525 | 25.551 |
| Net-new tokens | 34,595 | 64,092 |
| Candidate lines | 89 | 70 |
| Sampled peak condition RAM | 0.896 GiB | 0.795 GiB |
| Sampled peak interval-average CPU cores | 1.033 | 0.841 |

N's terminal policy violation arose from the specific read-only shell command
`ls -la /workspace && lean --version && printenv LEAN_PATH`. The historical
policy rejected both the `printenv` token and `LEAN_PATH` substring even though
the open-snapshot design deliberately exposes the mounted library path. This
was not a source-faithfulness verdict. The candidate was not audited, and its
numbers must not be used as a faithful comparison. Its frozen candidate SHA-256
is `c2ee1c205ac9ccc227c635afb23cee78a897e30c8da626420e5585d8a2c7b1c5`.

L's candidate SHA-256 is
`0214d697ab5b154302c7e05f448e5d75b95274de951964731c3bcb4d4637e857`.
It compiled and passed proof integrity. The independent direct and round-trip
judges both returned `faithful-stronger`; their outputs contain all 16 semantic
checks, and the direct judge accounted for 72 recursively imported semantic
dependencies. No adjudication was triggered. The audit decision SHA-256 is
`94145e42b6286d7b858cbaa776b87dde6cfca676e87c5c372d9d02077636c889`.
The private dossier confirms direct use of `NumStability.fl_recursiveSum` and
`NumStability.fl_higherPrecisionRecursiveSum` along with the foundational
FP/gamma interface. Auditing itself took 394.348 s and 263,693 reported
tokens, excluded from the contestant clock but retained in the report.

**Decision:** do not resume Pilot 21's other tasks. Prospectively permit only
the exact `printenv LEAN_PATH` read under the open-snapshot policy, while still
rejecting general environment enumeration. Also restore the frozen-library
declaration-name feedback filter in both conditions. Keep task packets,
prompts, GPT-6 Sol high formalizers, Astra high auditors, resource caps,
admission evidence, and the warm root unchanged. A distinct Pilot 22 must be
launched with its own frozen controller commit and output directory. This
repair is justified by the concrete interface mismatch; the L acceptance and
unscored diagnostic timing do not authorize outcome-driven corpus selection.
