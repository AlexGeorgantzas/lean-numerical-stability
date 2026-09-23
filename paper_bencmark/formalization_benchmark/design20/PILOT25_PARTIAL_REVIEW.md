# Pilot 25 seven-task pause and prospective Pilot 26

Pilot 25 is an exploratory development run, not a held-out confirmation. Its
controller is frozen at `9a27c4e44`, with campaign artifacts at
`/hdd/alexgeorgantzas/highambench/pilot25-development-12-20260923-a`.
The first-pair review is recorded separately in `PILOT25_FIRST_REVIEW.md`.
No Pilot 25 input has been edited or measured task silently rerun.
The campaign stopped at `PAUSED_CONCURRENT_INCIDENT` after seven of twelve
scheduled tasks; the final `campaign.json` SHA-256 is
`f7780d8bd61c6a9b7a24b9dd5d6e71d8bb83cf02c0aa1aba25e61f3df0942ccc`.

| Task | Sealed pair status | L/N contestant-system time | Interpretation |
| --- | --- | ---: | --- |
| RUMP12-THM3.4 | Audited faithful pair | 1.031 | Near tie; L directly used finite-format interfaces. |
| FAB19-EQ3.5 | Audited faithful pair | 0.621 | L faster and shorter, but used more tokens; both required one repair. |
| FAB19-EQ3.7 | Ineligible | — | N used prohibited root-wide `find /`; L passed. No paired effect. |
| H20-8 | Audited faithful pair | 1.239 | L slower, though shorter; direct least-squares declarations used. |
| RUMP12-THM3.5 | Pair incident | — | N enumerated the environment; L's judges repeatedly returned schema-contradictory faithful records. |
| FAB19-EQ3.6 | Ineligible | — | Both conditions exhausted four unfaithful submissions. |
| CAST08-PROP3.2 | Audited faithful pair | 0.973 | L slightly faster and shorter, with more tokens. |

The four sealed eligible pairs above are the entire Pilot 25 paired-effect set.
Their descriptive geometric-mean L/N contestant-system time ratio is 0.937;
L used about 1.38 times as many net-new tokens and produced about 0.83 times
as many candidate lines. This tiny adaptive sample is not a confirmatory
estimate or evidence that the library generally improves speed.
The ineligible and incident rows must not be counted as L wins or losses, and
the FAB19-EQ3.6 row is not a faithful-pair time comparison. The other five
scheduled tasks never started. The campaign will not be resumed with altered
inputs. The final FAB19-EQ3.6 pair report SHA-256 is
`a3fcad11e924abb94339a8ef14af06ef2bac4799e637bb4380581290a9b31e81`.

## Incident evidence and prospective response

The two N interface violations were different broad-inventory commands:
`find /` on FAB19-EQ3.7 and `env | rg 'LEAN|LAKE|MATHLIB'` on
RUMP12-THM3.5. The latter was an apparent attempt to find the Lean path, but
the frozen rule permits only the specific `printenv LEAN_PATH` query. Neither
candidate received a faithfulness verdict after the violation.

The RUMP12-THM3.5 L audit rejected fresh direct and round-trip judgments that
called the statement faithful while also populating fields reserved for
candidate/source mismatches or unresolved uncertainties. The direct records
described a possible flaw in the source proof under arbitrary tie choices;
round-trip records described additional coverage as strengthening. The strict
schema validator correctly refused internally contradictory accepted records.
This is an audit-system incident, not an unfaithfulness decision.

Pilot 26 prospectively clarifies the same safe exploration commands to both
formalizers and clarifies auditor field semantics without weakening the
validator or the 16-check, dependency, implication, and adjudication rubric.
It also refills the same three isolated 8-CPU/24-GiB lanes on completion rather
than idling at a three-task batch barrier. The source PDFs, packets, library
snapshot, model identities, four-submission limit, and contestant/audit clock
separation are unchanged. The same twelve tasks are retained, with
RUMP12-THM3.5 first as a development canary. This is outcome-aware pilot
development and must never be represented as a held-out effect estimate.

The first completed parallel batch had ten formalization submissions. Its
largest sampled per-lane memory use was 0.99 GiB; largest one-second-mean CPU
use was 1.34 cores; no OOM events were recorded. Every lane's 8 logical CPUs
and 24 GiB limit are independently logged before and after attempts.

The Pilot 25 controller and its active lane exited before any Pilot 26
preflight or measurement began; no measured campaigns overlapped.
