# Pilot 29/31/32 proof-required ten-task report

Generated from the frozen, hash-checking `pilot32/composite_report.py` on Titan on
2026-09-24. This is a **descriptive, outcome-aware recovery composite**, not one
uninterrupted or held-out experiment. Pilot 29 contributed five sealed pairs,
Pilot 31 four, and Pilot 32 one. Interrupted partial attempts remain separate
incident evidence and are not spliced into results.

## Primary outcomes

- Ten tasks were scheduled; eight pairs had eligible faithful statements and
  six pairs had complete, kernel-checked proofs in both conditions. Four pairs
  had proof attrition or an incident.
- Across the **six both-proved pairs**, L used 1,265 nonblank Lean code lines in
  final proof files versus N's 2,008 (37.0% fewer). L was shorter on all six.
  Inclusive contestant-system time was 3,122 versus 4,116 seconds (24.2% less)
  and L was faster on five of six. L consumed 1,170,207 versus 719,566 net-new
  tokens (62.6% more).
- Five of the six both-proved pairs directly reached a NumStability declaration
  in L's elaborated **statement**. On this descriptive subset, L used 934 versus
  1,641 proof-code lines (43.1% fewer) and 2,474 versus 3,493 seconds (29.2%
  less), but 995,968 versus 624,407 tokens (59.5% more). These are post-hoc
  subset figures, not a causal estimate.
- Across the eight eligible faithful-statement pairs, L used 334 versus 387
  statement-code lines (13.7% fewer), but was shorter on only four individual
  tasks. The strongest size result is therefore in **completed proof files**.
- The elaborated L statement directly reached NumStability on seven of ten
  scheduled tasks. This is not a separate proof-body dependency audit.

Times below are inclusive contestant-system seconds, N/L. Proof lines count
nonblank Lean code in the final proved file; they are reported only where
**both** conditions proved faithful frozen statements. `Yes` in the reach
column means direct elaborated *statement* reach, not merely an import.

| Task | Status | N/L time (s) | N/L proof-code lines | L direct reach |
|---|---|---:|---:|---|
| CAST08-FIXED3 | Both faithful, both proved | 555 / 522 | 263 / 197 | Yes: FP model, dot product, recursive sum, gamma |
| RUMP12-THM3.4 | Both faithful, both proved | 944 / 619 | 517 / 214 | Yes: finite-format interface |
| FAB19-EQ3.6 | Both faithful, neither proved | 1,369 / 427 | — | No |
| LL07-THM4 | Both individual statements accepted; proof-stage incident | 3,273 / 929* | — | Yes: finite-format interface |
| CAST08-PROP3.2 | Both faithful, both proved | 791 / 553 | 292 / 225 | Yes: FP model and recursive sum |
| H20-8 | Both faithful, both proved | 506 / 264 | 272 / 112 | Yes: least-squares interfaces; no FP model |
| RUMP12-THM3.5 | Both faithful, neither proved | 909 / 1,444 | — | Yes: finite-format interface |
| CAST08-PROP3.1 | Both faithful, both proved | 696 / 516 | 297 / 186 | Yes: FP model and recursive sum |
| LL07-THM7 | Infrastructure incident before contestant work | — | — | Not available |
| FAB19-EQ3.5 | Both faithful, both proved | 623 / 648 | 367 / 331 | No |

`*` LL07-THM4 times are preserved observations, **excluded** from paired
comparisons. N's fourth proof turn failed usage telemetry validation; L
exhausted the proof-attempt limit. FAB19-EQ3.5 is the one both-proved pair
where L was slower, and its L statement had no direct NumStability reach.
RUMP12-THM3.5 was slower in L and neither condition completed a proof.

## Incidents and limits

1. Pilot 29 was interrupted by Titan downtime. Five sealed pairs were kept;
   its three partial pairs were preserved separately. Pilot 31 restarted only
   the three interrupted and two unstarted tasks, with fresh N/L conversations.
2. Pilot 31 sealed four more pairs. Its LL07-THM7 pair was interrupted after N
   exhausted its proof attempts and while L's proof work was incomplete; that
   partial pair was **not** counted.
3. Pilot 32 attempted only LL07-THM7 with fresh N/L conversations. Its
   ten-line `import Mathlib` template exceeded the fixed 600-second compiler
   preflight limit before either contestant began. The pair was sealed as an
   infrastructure incident; it supplies no N/L effect estimate. Root-disk
   space was 3.2 GiB at completion, so disk exhaustion is not established as
   the cause of this compiler timeout.
4. Sampled peaks across recorded contestant work reached 7.86 CPU cores and
   3.95 GiB RAM. Sampling may miss brief spikes. The high CPU peak, from an
   unsuccessful LL07-THM4 N turn, means that halving CPU allocations to four
   cores is **not yet qualified** even though 12-GiB RAM lanes look plausible.
5. These ten tasks were selected after earlier pilot outcomes were known.
   The results demonstrate where this frozen library and workflow helped and
   where they did not; they do not estimate performance on an unbiased task
   population. The primary time measure includes contestant-side discovery
   and compilation. Audit effort is logged separately, outside benchmark time.

## Provenance

- Pilot 29 journal SHA-256:
  `423bf0fe15961a0d731662a8927f21454d6792997cab2feb99a8a4186c05ca62`
- Pilot 31 journal SHA-256:
  `7ce2be6e5cb98b6a9f30f2aee5f73f7b41115687dc3ac4e33d728bf9dc1a2c51`
- Pilot 32 journal SHA-256:
  `2887eab06ce9ed820357470f8cd916ba759aa16bf3e491296ad5cf6954685954`
- Pilot 32 recovery manifest SHA-256:
  `10864bb0515c1801703938976eb80da630a7a0533680ffc103fa1cc0f9b324db`
- Frozen composite-report script SHA-256:
  `54d58330334fe895e95d94a37aa95561270e9db134982defe9e607843088114b`
- Pilot 32 controller commit: `f9e65cd2737a8540a58b597ee300b3535ec522e7`.

The report script verifies the frozen inputs, journal identities, all ten
sealed pair hashes, and the preserved partial evidence before calculating its
summary. Source artifacts remain on Titan under
`/hdd/alexgeorgantzas/highambench/pilot{29,31,32}-*`.
