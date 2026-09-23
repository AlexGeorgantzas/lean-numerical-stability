# Prospective full-corpus screen — not frozen or admitted

This is a development worklist, **not** a scored corpus. Pilot 27's first
measured canary began before this note; its inputs cannot be changed. Prior
Pilot 26 outcomes are known and will be disclosed for every reused task.

## Strict gate

Before a task enters a later 10–15-task campaign:

1. Hash-verify the exact source PDF and clarify the complete result/domain.
2. Rule out a NumStability result already proving the target (including a
   stronger theorem under another name).
3. Compile a *private, source-faithful statement skeleton* that directly
   reaches a compatible task-relevant NumStability algorithm/error interface.
   An import, `FPModel`, `gamma`, or an unrelated helper is insufficient.
4. Independently review that skeleton against the source. Keep it inaccessible
   to N and L contestants. Pin the library snapshot and evidence hashes.
5. Classify genuine difficulty before seeing new-pilot outcomes. Select 2–4
   hard but in-scope tasks, with variety where this does not compromise gates.

## Existing candidates

| Task | Evidence so far | Open gate |
|---|---|---|
| FAB19-EQ3.5 | Pilot 26 audited faithful L statement directly uses FPModel, `fl_recursiveSum`, `fl_higherPrecisionRecursiveSum`; hard. | Pilot 27 proof canary underway. |
| FAB19-EQ3.6 | Pilot 26 audited faithful L statement directly uses FPModel, `fl_recursiveSum`, `fl_kahanSum`; hard. | Pilot 27 proof canary pending. |
| CAST08-FIXED3 | Pilot 26 audited faithful L statement directly uses FPModel, `fl_dotProduct`, `fl_recursiveSum`. | Pilot 27 proof canary pending. |
| H20-8 | Pilot 26 audited faithful L statement reaches `lsNormwiseBackwardErrorMatrixOnlyEtaF` and associated feasible/cost interfaces. | Good direct error-interface overlap, but does not require FPModel; decide whether this is an explicit exception. |
| CAST08-PROP3.2 | Source-reviewed t-level superblock dot product; `fl_dotProduct` and `fl_blockDotProduct` were screened as components, and Pilot 26 L statement was shorter. A new **private** statement candidate with `fl_dotProduct` as the level-one block compiled and passed source-integrity validation on Titan (SHA-256 `0030d21b33ea9652ef47594c1e80e3284f9b2ff55c4879ad76dd61bd49f2b209`). | Its semantic direct reach and independent source-faithfulness audit remain unverified. No admission yet. |
| P14-T1, P14-T2 | Original source packets and PDF hash exist. The paper's recursive denominator summation is topically related to NumStability `fl_recursiveSum`. The prior accepted P14-T2 L candidate (Pilot 6) imported only Mathlib and used a relational per-operation trace. | A deterministic `FPModel` algorithm does not automatically cover every independently varying trace. No strict admission without a source-preserving operational bridge, collision review, and a new compiled/audited private skeleton. Do not reuse the original common scaffold in N. |
| H20-6, H20-9 | Source packets exist; least-squares interfaces are present. | Check FPModel relevance, target collision, actual algorithm/error reach, and complete source-faithful skeletons. |

## Not admitted from the old twelve-task set

RUMP12-THM3.4/3.5 and LL07-THM4/7 used finite-format or different operation
representations in their prior accepted L statements; no compatible direct
algorithm/error reach was shown. FAB19-EQ3.7 and FAB19-THM4.1 used relational
per-operation error models incompatible with the current deterministic
`FPModel` algorithms; the accepted L statements did not reach a NumStability
declaration. FAB19-THM4.2 had an ineligible N pair and no direct L reach.
They remain possible future tasks only after an honest bridge and fresh gate.

H5-5 and H23-6 are excluded for likely target-result leakage as documented
in `CORPUS_SCREEN_NOTES.md`. Do not fill the desired count with them.

At present only the three Pilot 27 canaries unquestionably meet the combined
FPModel + direct-algorithm + prior-audited-candidate gate. A ten-task campaign
must not be declared ready merely because ten packet IDs can be listed.
