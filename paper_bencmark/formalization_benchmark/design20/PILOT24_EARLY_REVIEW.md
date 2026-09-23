# Pilot 24 first-pair review and prospective Pilot 25 decision

Pilot 24 is an exploratory development pilot, not a confirmatory comparison.
Its frozen controller is `c90e2474e`; the campaign at
`/hdd/alexgeorgantzas/highambench/pilot24-development-12-20260923-a`
stopped at its mandated `PAUSED_FIRST_REVIEW` gate after exactly one pair.
Do not resume it, edit its inputs, or pool its result with a successor pilot.

The `RUMP12-THM3.4` pair was an **audited-faithful pair**, with one compiling
submission and one complete independent faithfulness audit per condition.
Both used GPT-6 Sol/high; auditors used GPT-6 Astra/high. The L candidate
directly reached `NumStability.FloatingPointFormat` and its finite-system,
unit-roundoff, and nearest-rounding interfaces. There was no proof requirement.

| Metric | N / R0 | L / R1 | L/N |
| --- | ---: | ---: | ---: |
| Contestant system wall time | 144.424 s | 200.730 s | 1.390 |
| Contestant active time | 129.089 s | 174.428 s | 1.351 |
| Formalizer wall time | 128.874 s | 175.123 s | 1.359 |
| Automatic retrieval wall time | 15.335 s | 26.302 s | 1.715 |
| Net-new tokens | 40,111 | 72,521 | 1.808 |
| Candidate lines | 40 | 36 | 0.900 |

The unfavorable time/token outcome is preserved. The diagnostic defect is
specific and independently visible in the trace: L's task-neutral packet
surfaced `FPModel`, `gamma`, `fl_recursiveSum`, and a gamma-guarded bound,
but not `FloatingPointFormat` or `nearestRoundingToFinite`, although the
source title explicitly said “rounding to nearest” and L's final, audited
statement used those exact declarations. L issued multiple index queries
for “nearest binary floating underflow”, “round nearest representable”,
“finite binary format”, and then show requests for the finite-format
interfaces. This is an open-snapshot retrieval miss, not a reason to change
the source result, auditor rubric, or treatment condition.

The prospective Pilot 25 change is a **task-neutral lexical facet**: when
a positive source title concerns nearest/faithful finite-format rounding,
the router will include the public format and nearest-rounding interfaces
alongside ordinary component cards. The rule must apply to every task and
be tested against the complete frozen atlas before a new pilot is admitted.
The first task stays first. No library theorem or target result is added;
both conditions retain the same PDFs, the same audit, and the same clock.

Immutable evidence: campaign JSON SHA-256
`47ddb99da109b25b0a7b0ce555a8675a7262d6363bcdc550e82a3a12ee636c89`;
first pair report SHA-256
`168f94094f1d3727219a51e88ce2fd9dcc4b34feaa058c32b5535e92d87e301e`;
L formalizer events SHA-256
`559f5eac1445087fb2db9043689386b078dad4751d063847e614416920fbe793`.
