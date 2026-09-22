# Design17 statement-formalization campaign — 2026-09-22

## Executive result

The overnight Design17 campaign completed all 13 planned Higham tasks.

- 12 tasks produced an audited-faithful pair.
- H12-4 was correctly retained as an ineligible pair after both conditions exhausted four submissions without a faithful formalization.
- There were no infrastructure incidents and no unfinished audits.
- Every generated candidate compiled, passed proof-integrity checks, and was hash-frozen before its audit.
- The campaign is deliberately labelled `UNSCORED_ENGINEERING_EXPLORATORY`. It does not report a pooled treatment effect.

The primary comparison is encouraging but small: both tasks selected in advance as having useful NumStability building blocks without the target result favored condition L on contestant-active time and final lines of Lean. H5-5 was a large win; H10-7 was a modest active-time win and essentially a tie on system time after retrieval overhead. With only two primary tasks, this is promising engineering evidence, not a powered scientific conclusion.

Condition mapping:

- R0 / N: Mathlib only.
- R1 / L: the same environment plus the frozen NumStability snapshot and its generated composition packet.

All ratios below are R1/R0, so values below 1 favor the library condition.

## Primary engineering stratum

| Task | Faithfulness | Route R0 → R1 | Active seconds R0 / R1 | Active ratio | System seconds R0 / R1 | System ratio | Net-new tokens R0 / R1 | Token ratio | Final lines R0 / R1 | Line ratio | Submissions R0 / R1 |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| H5-5 | both faithful | direct/composition → direct/composition | 662.938 / 394.707 | **0.595** | 680.435 / 429.871 | **0.632** | 86,336 / 41,601 | **0.482** | 75 / 29 | **0.387** | 2 / 1 |
| H10-7 | both faithful | no route → direct/composition | 529.829 / 506.831 | **0.957** | 543.421 / 540.628 | **0.995** | 53,761 / 59,014 | 1.098 | 99 / 82 | **0.828** | 1 / 1 |

Interpretation:

- H5-5 shows a clear library benefit across time, tokens, lines, and submissions. Some of the margin comes from R0 requiring a faithfulness repair, which is part of the measured workflow but must be disclosed.
- H10-7 is the cleaner one-submission comparison. L saved about 4.3% active time and 17.2% of the final lines, but spent 9.8% more net-new tokens. Its larger retrieval cost erased almost all of the active-time saving in total system time.
- Descriptively, both primary active-time ratios and both line ratios favor L. No aggregate estimate or significance claim is justified from two tasks.

## Negative controls

These tasks had no approved NumStability route in either condition. Their mixed results estimate task/model variation; they are not evidence for or against a library treatment.

| Task | Outcome | Active seconds R0 / R1 | Ratio | Tokens R0 / R1 | Lines R0 / R1 | Explanation |
|---|---|---:|---:|---:|---:|---|
| H22-11 | both faithful | 549.429 / 460.635 | 0.838 | 80,717 / 41,490 | 101 / 97 | Favorable L result with no route; treat as process variation. |
| H20-6 | both faithful | 1029.274 / 869.753 | 0.845 | 124,977 / 73,403 | 244 / 202 | R0 required a repair; no library route. |
| H7-12 | both faithful | 189.633 / 207.569 | 1.095 | 23,049 / 15,730 | 37 / 46 | Mild time loss but fewer L tokens; no route. |
| H12-4 | pair ineligible | 1636.667 / 1524.477 | — | 225,215 / 130,279 | 139 / 105 | Both conditions exhausted four submissions. The source packet did not pin down the referenced fast-correction contract sufficiently to establish full-domain coverage. |
| H19-5 | both faithful | 450.878 / 476.909 | 1.058 | 73,846 / 54,727 | 77 / 89 | Mild time and line loss but fewer L tokens; no route. |
| H7-14 | both faithful | 377.312 / 378.238 | 1.002 | 43,387 / 36,383 | 109 / 111 | Effective time tie; no route. |

The controls show why small single-task differences are not persuasive. Ratios range in both directions even when the router gives neither condition a NumStability route.

## Excluded collision/router diagnostics

These five tasks were kept for diagnosis but excluded from treatment-effect inference because screening found result collisions, topical false positives, router errors, or unresolved near-collisions.

| Task | Faithfulness | Route R0 → R1 | Active seconds R0 / R1 | Ratio | Tokens ratio | Lines ratio | Diagnostic interpretation |
|---|---|---|---:|---:|---:|---:|---|
| H22-5 | both faithful | direct/composition → direct/composition | 552.776 / 524.403 | 0.949 | 0.894 | 0.788 | Topical false positive; diagnostic only. |
| H20-9 | both faithful | no route → direct/composition | 352.062 / 502.741 | 1.428 | 1.364 | 1.211 | L required a domain repair and the result family is already present; exclude. |
| H20-8 | both faithful | no route → no route | 596.369 / 312.654 | 0.524 | 0.775 | 0.912 | R0 required a repair; hidden direct-result collision and router false negative. |
| H23-6 | both faithful | no route → no route | 603.602 / 730.444 | 1.210 | 1.101 | 1.053 | Strong router miss: useful Strassen/Winograd components exist, but no single visible signature covered the full algorithm/rounding/norm contract. |
| H15-3 | both faithful | no route → no route | 839.523 / 912.432 | 1.087 | 1.132 | 1.035 | Both conditions repaired an incorrect `n ≥ 5` restriction; unresolved content-near-miss, so diagnostic only. |

These results cannot be pooled with the primary stratum. H23-6 is nevertheless the most useful architecture diagnosis in the campaign.

## What changed and what worked

The campaign did not keep timing blind exploration of the entire library. It used a frozen, prebuilt declaration atlas and generated a bounded, typechecked composition packet for L. Task-specific retrieval was logged separately; the primary clock was contestant-active time, while system time retained retrieval overhead as a secondary metric.

The audit retained the depth required by the paper-derived protocol:

- fresh, stateless, condition-blind blind-translation, direct, and round-trip agents;
- per-dependency accounting;
- the mandatory 16-item semantic checklist;
- both implication directions;
- binary faithful/unfaithful decisions;
- adjudication on disagreement or unresolved uncertainty;
- no partial-domain pass and no acceptance of a stronger theorem unless it covered the complete source domain.

Blind translation and direct judgment ran concurrently; round-trip judgment began after blind translation. Repairs necessarily waited for the audit whose feedback they consumed. Formalizer conditions and tasks remained sequential to preserve the fixed hardware envelope and avoid provider-contention timing artifacts.

Operationally, the 26 condition runs used 8,370.293 seconds of R0 active time and 7,801.795 seconds of R1 active time. Auditing consumed 18,709.342 seconds of condition-level wall time and 15,177,524 auditor tokens, all logged and excluded from benchmark metrics. The audit was therefore not a shortcut.

## Architecture diagnosis

The remaining problem is treatment delivery, not simply library quality.

1. **The router is too all-or-nothing.** It often demands one declaration whose visible signature nearly covers the complete target contract. Real reuse is compositional: an algorithm definition, an FP model, a `gamma` lemma, a norm estimate, and an error theorem may each contribute separately.
2. **Retrieval overhead still matters.** H10-7 saved active formalization work but its 33.797-second L retrieval step erased the time advantage in system time. A useful package must make relevant components cheap to locate.
3. **Source packets need a semantic-completeness gate.** H12-4 passed structural preflight but referred to a fast-correction result whose necessary contract was not frozen precisely enough. Four repairs per condition could not repair missing source information.
4. **Single runs contain substantial variance.** The no-route controls produce both apparent wins and losses. Small effects should not be interpreted without repeated, counterbalanced runs.
5. **Collision screening must remain strict.** The excluded tasks demonstrate that an attractive numerical result can be caused by a hidden target-family result or by repair asymmetry rather than reusable building blocks.

## Recommended next design

### 1. Replace theorem-level routing with component-level routing

Build the L packet from independently scored components rather than requiring a near-complete declaration:

- algorithm semantics and data structures;
- floating-point model and `gamma` infrastructure;
- perturbation/backward/forward-error primitives;
- norm and condition-number lemmas;
- bridge lemmas between the relevant representations.

Each card should contain the exact typechecked signature, owning module, short task-neutral semantic description, and dependency closure. The packet should disclose why each component was selected, cap each category, and reject declarations that state the target result. This directly targets the H23-6 failure without inserting a gold theorem.

### 2. Add a semantic source-contract preflight

Before any measured run, use an independent source-side pass to verify that every referenced equation, algorithm, parameter range, stopping rule, and selected conclusion is present in the frozen source packet. Freeze and hash that contract. This is off-benchmark preparation and must not see either condition's candidate. A task failing this gate is repaired or excluded before consuming formalizer calls.

### 3. Preserve both active and end-to-end timing

Keep contestant-active time as the primary measure of formalization work, but continue reporting retrieval time and end-to-end system time. This prevents hiding package-discovery cost while still separating one-time/indexing infrastructure from task work.

### 4. Validate the mechanism before another large campaign

Do not spend another night on 13 tasks immediately. First:

1. implement component packets;
2. rerun only H23-6 as a router canary, marked diagnostic;
3. inspect whether the packet now exposes the expected algorithm, FP, and norm components without the target theorem;
4. rerun H10-7 as the clean primary canary;
5. proceed to the remaining primary corpus only if routes are materially better and the candidates remain independently faithful.

This is a mechanism gate, not tuning against the desired answer: success means correct component delivery and faithful outputs, not a favorable timing ratio.

### 5. Power the eventual thesis comparison

After the mechanism is frozen, run multiple counterbalanced repetitions on a larger set of genuinely eligible tasks. Keep the current cold/warm and excluded results as engineering evidence, but do not mix them with the final treatment estimate.

## Reproducibility and integrity

- Controller/runner commit: `c5c279d3dff674f9b91c5a774f8db76eac487431`
- Campaign identity: `2c81e04a24ad9563b36a30e4ed4cdf013ccf354e30a4c80db00e2c891f0f0fb2`
- Campaign outcome: `AUDITED_CAMPAIGN_WITH_INELIGIBLE_PAIRS`
- Campaign manifest SHA-256: `788b365158613bd3c02924a28bfea4dff7adda7407288f7dcbf3428936c72947`
- Manifest payload SHA-256: `e3f8846cd47ca91feab2cb4f1265bc5451cc51ac3ecab75b1ff6006b1a213afd`
- Frozen-input closure SHA-256: `b7f952780c348dae209cd4c189c5628f3e9eac93479c418641d57624bec86c59`
- State journal: 28 records; head `dcb620a802d0e54a26d05c82e82095ebcd48ef9a56ab2cb928ba43ec177082a1`; file SHA-256 `dd0b3e3d1175b7f721a86f73509dc75daf128f7f5c6fdfd25aadc028a0c85fe3`
- Summary journal: 28 records; head `07863b3ba2d88366f8a6c340d563f3778fc8d413421da4de870fb548c75cd502`; file SHA-256 `9e32e4bff0dad5d6e185438f31c74f0d9bae126de4cf09c32d93bf1421922b3a`
- Authenticated JSON report SHA-256: `9df42f55cd00254809a08351464cc05f28fc0c32617536456a8fd2c1accb49f2`
- Authenticated generated Markdown SHA-256: `90f012db9483f6dd94fcf77a9625c75745946e9709b36c5d7fcafaae01b530b2`
- Hardware: Titan, 13th Gen Intel Core i9-13900K, CPUs 0–7, 32 GiB RAM, no swap, 512-task limit.
- Formalizer: `gpt-5.6-sol`, `xhigh`.
- Auditors: `gpt-6-astra`, `high`.

An independent read-only closure sweep verified both 28-record journal chains, all 13 exact pair attestations, 3,411 attested files, 38 candidate/validation/audit triples, 76 admitted before/after hardware snapshots, and 70 explicit frozen-file references. All 13 runner return codes were zero and all runner stderr files were empty. No network-violation bytes were recorded.

One operational warning is retained for transparency: 36 of the 38 formalizer stderr logs contain the same recoverable 168-byte `apply_patch` verification message about multiple operations targeting `Candidate.lean`. Every affected attempt subsequently produced a hash-frozen candidate with a passing Lean validation and completed audit. This does not invalidate the integrity gate, but it may have added a small amount of contestant overhead and should be removed before a future powered campaign.

The full frozen NumStability build used commit `45813a95dacf577461bae13f033af0dbc985a225`, Mathlib `e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`, and Lean `v4.29.0-rc3`. It completed in 21:55.16 elapsed time (6,499.55 user seconds, 440.06 system seconds, 527% CPU), peaked at 8,406,028,288 bytes RSS, and produced 879 OLean files totaling 1,015,839,912 bytes. The library was built once and reused; it was not rebuilt for every task.

Titan evidence remains at:

- campaign: `/hdd/alexgeorgantzas/highambench/design17-statement-campaign-20260922-d`
- authenticated report: `/hdd/alexgeorgantzas/highambench/design17-statement-campaign-20260922-d-report-v1`
- preflight: `/hdd/alexgeorgantzas/highambench/design17-preflight-2a8fbfe9d/preflight-result.json`
- deployment: `/hdd/alexgeorgantzas/highambench/deployment-design17-v3-1f300018c/deployment.json`

No private chain-of-thought is included. The retained evidence contains prompts, candidates, observable tool events, usage, timing, compilation/integrity results, audit outputs, hashes, and condition-neutral repair feedback.
