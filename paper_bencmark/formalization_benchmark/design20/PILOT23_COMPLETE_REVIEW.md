# Pilot 23 complete: three audited development pairs

Titan campaign: `/hdd/alexgeorgantzas/highambench/pilot23-dev3-20260923-a`.
The immutable `campaign.json` SHA-256 is
`7644924f90e5d3507303eee957e8ab381f8507f4876f790b8c8d883372bb29f7`.
Controller commit: `46c7dc8643b8d69a02ce63cd6f23a4d78f95a228`.
The first pair was reviewed before the two other tasks ran concurrently in
independent eight-CPU, 24-GiB lanes. No Pilot 19–22 result was overwritten or
silently rerun. All three pairs finished in one submission per condition, with
both statements passing the binary faithfulness audit.

| Task | L direct use? | N system-wall s | L system-wall s | L/N | N active s | L active s | N/L net-new tokens | N/L lines |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| FAB19-EQ3.5 | Yes | 194.5 | 171.6 | 0.882 | 179.9 | 146.2 | 24,434 / 49,164 | 70 / 56 |
| FAB19-EQ3.7 | **No** | 211.6 | 244.5 | 1.156 | 197.9 | 218.4 | 40,846 / 63,053 | 55 / 85 |
| H20-8 | Yes | 105.5 | 126.2 | 1.196 | 91.3 | 100.7 | 26,076 / 61,324 | 39 / 27 |

Pair-report SHA-256 hashes, in table order:
`465ab519fae90e7b01f4626a801e12fa1a284155e39a94bb94a9e1fb01da491e`,
`51b6b2b0d169fa8d2f745508ae37895fa290f4fe4f4af57776ea508b59c9debe`,
`4304a1ec6a73e26a466d6696764c815da1783060cbae7f5c184f20141e321bcd`.

The treatment reached actual imported declaration references for FAB19-EQ3.5
(`fl_recursiveSum`, `fl_higherPrecisionRecursiveSum`, `FPModel`, `gamma`)
and H20-8 (`lsNormwiseBackwardErrorMatrixOnlyEtaF` and its interface).
FAB19-EQ3.7's L router exposed `fl_recursiveSum` and
`fl_clog2PairwiseSum`, yet the L formalizer chose a task-local relational
`RoundedAdd` model, `RecursiveSum`, and `PairwiseSum` and imported only Mathlib.
This pair is an audited workflow observation, **not evidence of direct library
benefit**. The observed non-use must remain visible in every summary; its
candidate should not be recoded as a treatment success.

L retrieval took 25.5, 26.0, and 25.5 seconds versus N's 14.6, 13.6, and
14.2 seconds. L also used more net-new provider tokens in every task. These
costs are not hidden by its shorter statement on two tasks. Audit time and
tokens were logged separately and excluded from contestant scores; the six
audits took approximately 303–509 seconds each. The detailed first-pair audit
and hardware evidence is in `PILOT23_FIRST_REVIEW.md` and the immutable Titan
artifacts.

Interpretation: two directly treated pairs give one L win and one L loss in
contestant system-wall time. This is small, correlated exploratory evidence,
not a reliable library-effect estimate. The third pair tests whether the
retrieval interface causes usable declarations to be adopted; here it did
not. The frozen prospective expansion queue remains a **candidate queue**.
Before a new twelve-task pilot, each proposed task still needs independent
source review, an exact component/collision check, and a compiling full-domain
private statement skeleton. A failure of any gate excludes the task regardless
of predicted or observed N/L performance.
