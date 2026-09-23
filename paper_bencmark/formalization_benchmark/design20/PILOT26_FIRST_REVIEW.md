# Pilot 26 first-pair review and continuation

Pilot 26 uses controller commit `00d8ba371`, corpus
`CORPUS_12_PILOT26.json`, and frozen Titan campaign
`/hdd/alexgeorgantzas/highambench/pilot26-development-12-20260923-a`.
The twelve-task static preflight passed all twenty-four N/L checks (SHA-256
`a76ca3965cda309d3557f3b2a849ae83f1add2907ead3893f01abc746fd048ac`);
the refreshed hash-verified admission passed all twelve tasks (SHA-256
`1e905517311cb80dc513234f47a4e139c7f26f75cb9a0e7b75db7096942c93cc`).
Pilot 25 remains separately frozen at `PAUSED_CONCURRENT_INCIDENT`.

The first Pilot 26 pair, RUMP12-THM3.5, stopped at `PAUSED_FIRST_REVIEW`
before any other measured task started. Both GPT-6 Sol/high formalizers
submitted once. Both candidates passed the exploration policy and Lean
compilation/integrity checks, and both were accepted by the full independent
GPT-6 Astra/high faithfulness audit. L directly imported and used
NumStability floating-point-format interfaces. Its blind, direct,
round-trip, and adjudicator roles all returned accepted schema-valid records
on one try; the final adjudicated verdict was faithful. The Pilot 25 L
audit's contradictory faithful-output incident did not recur.

| Metric | N / R0 | L / R1 | L/N |
| --- | ---: | ---: | ---: |
| Contestant system wall time | 234.828 s | 249.150 s | 1.061 |
| Contestant active time | 219.545 s | 221.283 s | 1.008 |
| Net-new tokens | 52,155 | 64,590 | 1.238 |
| Candidate lines | 102 | 80 | 0.784 |
| Submissions | 1 | 1 | 1.000 |

L was 6.1% slower on the full contestant-system clock and used more tokens;
it produced a shorter statement. This is a near tie, not a speed win.
The full first-pair report SHA-256 is
`813e8df3b84de692d82c0689ff6a9f027bed6568c30dcc47673435cd144d5acc`;
the paused first-review journal SHA-256 is
`7f6b1eef7d4d24ddf709b7e922500424d505c26aa89fb5da81e0b5c029b1fc1b`.

The objective interface and audit-schema incidents targeted by Pilot 26 were
absent, and this first pair is effect-analysis eligible. The same frozen
campaign was therefore resumed with `--resume-after-review`. The remaining
eleven tasks use three isolated 8-CPU/24-GiB lanes refilled on completion.
Negative, unfaithful, no-use, and incident outcomes must remain in the record.
This adaptive development run is not held-out confirmatory evidence.
