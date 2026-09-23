# Pilot 25 first-pair review and parallel continuation

Pilot 25 at `/hdd/alexgeorgantzas/highambench/pilot25-development-12-20260923-a`
was launched from frozen controller `9a27c4e44`, the twelve-task corpus
`CORPUS_12_PILOT25.json`, and hash-verified admission
`ADMISSION_12_PILOT25.json`. The first scheduled pair, `RUMP12-THM3.4`,
stopped at `PAUSED_FIRST_REVIEW` before any later task started. Both GPT-6
Sol/high candidates compiled, passed the independent GPT-6 Astra/high
faithfulness audit, and were accepted on their first submission. L directly
used NumStability finite-format declarations; no treatment failure or audit
incident occurred.

| Metric | N / R0 | L / R1 | L/N |
| --- | ---: | ---: | ---: |
| Contestant system wall time | 206.544 s | 212.906 s | 1.031 |
| Contestant active time | 191.260 s | 184.412 s | 0.964 |
| Formalizer wall time | 191.055 s | 185.311 s | 0.970 |
| Automatic retrieval wall time | 15.284 s | 28.493 s | 1.864 |
| Net-new tokens | 32,140 | 58,417 | 1.818 |
| Candidate lines | 49 | 43 | 0.878 |

This is a near tie in full system time, not a speed win. The finite-format
router change had its intended *mechanical* effect: L's first-attempt trace
has 9 command calls, versus 21 in the preserved Pilot 24 trace, and it
began with the relevant `FloatingPointFormat` and nearest-rounding cards.
The two runs are stochastic, so the difference in elapsed time between
pilots is not attributed causally to the router without replication.
The one Pilot 24 pair remains separately preserved and unfavorable.

The full first pair report is SHA-256
`0e49ed5989ef39aab8644cdeb88358928ec6436d2581ecd49f0b1c265072e153`;
L's raw formalizer event log is SHA-256
`706ebc8b707cbd177aed4b34cfea8f1039484270c274f6ef7d02465788f8956b`.
Because the pair is eligible, the route defect was objectively corrected,
and no new integrity issue emerged, the **same frozen Pilot 25** was resumed
with `--resume-after-review`. The remaining eleven tasks run in batches of
three isolated eight-CPU/24-GiB lanes. All negative, unfaithful, no-use, and
incident outcomes must be retained and reported.
