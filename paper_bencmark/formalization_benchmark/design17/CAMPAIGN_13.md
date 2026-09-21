# Design-17 Higham 13-task campaign plan

Status: `PREDECLARED_CONSUMED_DEVELOPMENT`  
Machine-readable schedule: `design17/CAMPAIGN_13.json`

## What this campaign can establish

This campaign runs all thirteen frozen Higham tasks under the Design-17
statement-only, matched-retrieval protocol. It can establish whether the new
system behaves coherently and whether NumStability helps on these known cases.
It cannot be a confirmatory estimate on untouched data: the corpus, routing
policy, readiness labels, and protocol were developed with knowledge of these
tasks. H5-5, H10-7, and H7-12 are explicitly consumed Design-16 engineering
cases. Conservatively, every observation in this campaign is labelled consumed
development evidence.

No result sign, effect size, token count, line count, or audit outcome may alter
the schedule or a task's analysis stratum. A future confirmatory experiment
must freeze Design-17 and use new tasks that were not involved in its design.

## Fixed design

- R0 receives the bounded matched Mathlib retrieval interface.
- R1 receives the same interface and budget, extended with the frozen
  NumStability snapshot.
- The formalizer is `gpt-5.6-sol` at `xhigh`; audit roles use `gpt-6-astra` at
  `high`.
- Each condition has one initial submission and at most three repairs in the
  same persisted conversation, a cumulative 18,000-second contestant-active
  limit, and no token cap.
- Timed formalizers run one at a time on Titan. Compilation, integrity checks,
  dossier construction, auditing, and audit retries are logged off-clock.
- Condition order is the existing frozen N/L order translated to R0/R1. It is
  balanced 6/7 overall, 1/1 in the building-block stratum, 3/3 in negative
  controls, and 2/3 in diagnostics.

## Frozen schedule

| # | Wave | Task | Stratum | Order | Readiness disposition |
|---:|---|---|---|---|---|
| 1 | Engineering gate | H5-5 | Building-block primary | R0, R1 | Include primary engineering |
| 2 | Engineering gate | H10-7 | Building-block primary | R1, R0 | Include with strict audit |
| 3 | Engineering gate | H7-12 | Negative control | R0, R1 | Negative control only |
| 4 | Remaining controls | H22-11 | Negative control | R1, R0 | Negative control only |
| 5 | Remaining controls | H20-6 | Negative control | R1, R0 | Negative control only |
| 6 | Remaining controls | H12-4 | Negative control | R0, R1 | Negative control only |
| 7 | Remaining controls | H19-5 | Negative control | R1, R0 | Negative control only |
| 8 | Remaining controls | H7-14 | Negative control | R0, R1 | Negative control only |
| 9 | Collision/router diagnostics | H22-5 | Collision/router diagnostic | R0, R1 | Router topical false positive |
| 10 | Collision/router diagnostics | H20-9 | Collision/router diagnostic | R1, R0 | Direct result-family collision |
| 11 | Collision/router diagnostics | H20-8 | Collision/router diagnostic | R0, R1 | Hidden direct result/router false negative |
| 12 | Collision/router diagnostics | H23-6 | Collision/router diagnostic | R1, R0 | Hidden direct result/router false negative |
| 13 | Collision/router diagnostics | H15-3 | Collision/router diagnostic | R1, R0 | Pending content-collision boundary |

The engineering gate is an integrity gate, not a performance gate. If its
results are null or negative but the run is valid, the remaining ten tasks
still run. Only a campaign-integrity failure can halt the queue.

## Analysis strata and no post-hoc exclusion

All thirteen scheduled tasks remain in the final accounting.

1. **Building-block primary (2).** H5-5 and H10-7 have predeclared useful
   NumStability building blocks without a frozen judgment that the selected
   result itself is present. Audited faithful paired ratios are reported as
   consumed engineering evidence, not confirmatory evidence.
2. **Negative controls (6).** H22-11, H20-6, H7-12, H12-4, H19-5, and H7-14
   have no route under the bounded packet. Their results are reported as a
   separate null-routing stratum and are never used to dilute or inflate the
   building-block estimate.
3. **Collision/router diagnostics (5).** H22-5, H20-9, H20-8, H23-6, and
   H15-3 are run to test the router and direct-result guard. They are reported
   task by task and never pooled into a treatment-efficacy estimate, even if
   both candidates are faithful.

There is no pooled "13-task win rate" or pooled R1/R0 effect. The report must
show every task, including timeouts, unfaithful candidates, integrity
rejections, and incidents.

## Faithfulness and effect eligibility

`AUDITED_FAITHFUL_PAIR` requires both conditions to compile with exactly the
permitted final-target `sorry`, pass all integrity checks, and receive a binary
`faithful` verdict from the full condition-blind audit. That audit includes the
recursive dossier, per-dependency records, both 16-item semantic checklists,
both implication directions, and adjudication on the frozen triggers. Partial
domain or partial case-split coverage is unfaithful. A genuinely stronger
full-domain proposition may pass.

Only an `AUDITED_FAITHFUL_PAIR` without an incident contributes a paired time,
net-new-token, or line-count ratio. A condition that exhausts four submissions,
exhausts the cumulative active-time budget, never produces an integrity-valid
compiling statement, or ends unfaithful makes the pair
`AUDITED_PAIR_INELIGIBLE`. It remains a benchmark outcome and is not censored.
Success rates and every ineligibility reason are reported next to any
success-conditioned ratios.

## Stopping and incident rules

The campaign continues after an attributable contestant failure and after any
valid negative or unfavourable result. It halts before the next timed condition
when there is a threat to cross-task validity: a frozen-input or artifact hash
mismatch, hardware-envelope failure, uncertain time/token accounting, source
or condition leakage, source-packet/PDF/overlay mismatch, or a systematic
validator, audit, sandbox, provider, or controller failure.

An incident is preserved with its journal and artifacts. There is no silent
rerun. The same campaign may resume only when exact hash-verified recovery
shows that no completed observation, frozen input, or assignment changed. Any
protocol or input change creates a new campaign identity, and the two campaign
versions are not silently combined. Auditor infrastructure may be retried at
most twice against the same frozen candidate; this does not authorize a new
contestant submission.

## Input validation completed locally

The schedule fixes all thirteen packet paths and SHA-256 values, the sole H10-7
contract overlay, and all nine distinct chapter-PDF basenames and hashes. The
following deterministic checks passed before this plan was committed:

- the thirteen task IDs are unique and exactly match the readiness task set;
- each packet has the required closed-schema fields, the expected task ID, a
  valid SHA-256 PDF reference, and at least one source location, clarification,
  and scope constraint;
- each packet hash and PDF identity matches the frozen Pilot-15 manifest;
- H10-7 is the only declared contract overlay, its task ID matches, and its
  hash is fixed; no undeclared overlay exists for another scheduled task;
- two local copies of every referenced chapter PDF have the expected hash;
- `pdfinfo` reports the expected page counts, and every referenced PDF page is
  within its document; and
- the condition orders reproduce the frozen configuration and satisfy the
  stated balance counts.

These local checks do not substitute for launch-time validation. The Titan
campaign manifest must independently hash the actual deployment PDF root,
packets, overlay, prompts, schemas, controllers, atlases, snapshot records, and
hardware envelope before the first paid turn.
