# Pilot 27 first-pair incident and separate post-hoc check

The frozen Pilot 27 campaign at
`/hdd/alexgeorgantzas/highambench/pilot27-proof-canary-20260923-a` is
`PAUSED_FIRST_REVIEW`. Its only measured pair is `FAB19-EQ3.5` (pair-report
SHA-256 `fc291abaa473469991bb3bec158c2adebfa4a38118808d0dc633643ba2474040`).
Do not resume it or treat it as a completed proof-required pair. The proof
validator tried to use a scratch directory that the controller had not created.
Both measured proof submissions therefore have status
`PROOF_VALIDATION_INCIDENT`, not `PROVED_FROZEN_STATEMENT`.

| Condition | Audited faithful statement | Statement lines | Statement contestant wall | Statement net-new tokens | Frozen proof source lines | Proof turn wall | Proof turn net-new tokens |
|---|---:|---:|---:|---:|---:|---:|---:|
| N / R0 | yes, after 3 submissions | 96 | 467.8 s | 90,219 | 577 | 638.3 s | 75,725 |
| L / R1 | yes, after 1 submission | 78 | 203.3 s | 109,420 | 309 | 306.7 s | 42,836 |

These are observed source/effort diagnostics only. The measured proof effect is
ineligible. L's shorter source does **not** establish use of a task-specific
NumStability algorithm: the proof candidate reaches `FPModel`, its rounding
interface, and `gamma`, but not `fl_recursiveSum` or
`fl_higherPrecisionRecursiveSum`. This is a failure of the strict
algorithm/error-component uptake gate for this actual contestant output,
despite the earlier private admission skeleton showing that such an interface
was possible. The FAB19 paper's independently variable per-operation rounding
also creates a possible representation gap with fixed-operation library
algorithms. Do not narrow the paper domain just to force uptake.

After the pause, a **separate, off-clock diagnostic** at
`/hdd/alexgeorgantzas/highambench/pilot27-posthoc-proof-check-20260924-a`
ran the corrected controller's validator and semantic extractor on the two
unchanged frozen proof files. Both compiled without `sorry`; both semantic
hashes matched their respective audited statements:

| Condition | Proof candidate SHA-256 | Accepted = post-hoc semantic SHA-256 | Post-hoc validation SHA-256 |
|---|---|---|---|
| N / R0 | `0e09e33d4e80d2250b85d05f9201384d7411b82a66f195383624aec708848607` | `911940fe379f8ff1057efe2fa1b1cb7a8550732fff1974c5ad86def39099a85f` | `29c741b6aaaef3d831274f5520ea4dfa47b3646ea84448205fa27df98fc0677e` |
| L / R1 | `9b467ddc29bb07cffa97b937c9c4473a9dba600ab6a988cebdc63f8e7e488064` | `9ad9f640970c421ecc982794cc69b66d19666ee36d7d093ede0a9f91f97f30d8` | `25ccec7a7c640e7e3e3554f67244c9affd66ffa0193c27a90b482e506e50fb1e` |

The post-hoc check demonstrates that the infrastructure bug, rather than a
Lean failure, stopped the measured proof verification. It does **not** backfill
the immutable Pilot 27 verdict or license a scored proof ratio. Pilot 28 is a
new canary with a different pinned controller/corpus identity, fresh
contestant conversations, the scratch fix, and explicit proof-incident pause.
Its repeated task is disclosed as exploratory; neither condition sees the
Pilot 27 candidate or feedback.
