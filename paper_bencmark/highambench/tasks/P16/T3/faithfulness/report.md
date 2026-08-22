# Faithfulness audit: P16-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `b2fbda0cd4a25a550f5c1e6748f19106ede7893d7f407d99f6fde565c766e49a`
- Paper SHA-256: `8010a50989428b09ea9f204875cd6cfde6c08c924beb40887a6921287605737a`

## Decision

The authoritative PDF hash matches the supplied source. The complete declaration resolves the round-trip uncertainty: D001 and D026 are proof-carrying structures, and D036's previously hidden tail assumes the exact correction-level contraction estimates. D015 separately assumes the exact high-precision contributions. Consequently, the target's recurrences follow by composing assumptions that contain the substance derived on PDF pp. 40-41. The PDF proof also settles the implication direction for contraction factors: the actual forward and backward multipliers are bounded above by Lambda. The target does not reverse that direction, but it replaces the source conclusion with an additive recurrence and replaces qualitative first-order relations by exact inequalities. Its exactness is not a genuine stronger theorem over the paper's executions because applicability has been narrowed to runs already carrying the desired certificates. The structures are consistent enough to avoid literal vacuity, so the defect is truth for an unintended and substantially restricted reason. Together with the computed-object key conditions and fixed unrestricted polynomial, these facts make the statement different rather than merely weaker.

## Implications

- **Lean implies paper:** `no`. The Lean result applies only to proof-carrying runs that already contain exact correction contractions and exact high-roundoff bounds. It neither derives those facts from the paper's mixed-precision hypotheses nor states the paper's attainable floors. Its lambda_i < 1 condition also does not supply the paper's much-less-than-one regime. The PDF proof fixes the factor direction as actual factors no larger than Lambda, but the Lean recurrence plus an additive term is not that complete source conclusion.
- **Paper implies lean:** `no`. The paper provides first-order lesssim bounds with suppressed second-order terms, qualitative smallness, and generic low-degree constants. It does not entail exact per-step inequalities for one fixed polynomial, the altered computed-quantity key certificates, or the exact downstream bounds required by D015 and D036.

## Findings

- **critical / conclusion-assumed-as-input:** The target verifies a composition lemma over certificates already containing the selected result's central mathematical work.
- **major / conclusion-form:** The attainable-floor theorem and its common factor bound are not formalized as conclusions.
- **major / relation-and-remainder-mismatch:** The formal hypothesis is weaker in smallness while the formal inequalities are stronger in exactness, preventing either implication.
- **major / key-dimension-model:** The declaration's key certificate is attached to different mathematical objects from the source conditions.
- **major / constant-model:** The source's generic-bound convention is replaced by materially different quantified data.
- **minor / floating-point-domain:** Some formally admissible parameter interpretations do not have the intended standard floating-point meaning.
- **note / preserved-semantics:** These matches identify the intended theorem but do not overcome the mismatches in proof obligations and theorem content.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `fail` | `unclear` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `unclear` |
| `S06` | `fail` | `unclear` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `unclear` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `unclear` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `pass` |
| `S16` | `fail` | `unclear` |

## Dependency coverage

- Blind translator covered `116` dependencies (`0` hash-reused meanings); unclear: `D001, D026, D036`.
- Direct judge covered `116` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D007, D008, D009, D014, D015, D024, D026, D027, D028, D029, D030, D031, D036, D037`.

## Remaining uncertainties

- The PDF does not specify coefficients for c(n,k), permits the notation to vary by occurrence, and does not resolve how the displayed generic k should be chosen uniformly from the restart-dependent k_i.
- The qualitative relations much less than, much greater than, and lesssim have no numerical thresholds or quantified second-order remainders in the PDF.
- Theorem 6.3 does not explicitly clarify whether every additional hypothesis of Theorem 4.1, particularly iterate-norm comparability and the extra backward-rank condition, is automatic from (6.17) or remains inherited.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/agent_outputs/adjudicator.json` (`022547966d2fa79043cc01e06db74744e33721cf2e3869b9047364d8a8cd47a8`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/agent_outputs/blind_translation.json` (`2452b047925c0c6fcbb3078310a1e6fda2839bd80945d2f77b2a5d5b48c1710c`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/agent_outputs/direct_judge.json` (`6ce1789bc5938bcb158b8674d09bd6a0f6493b2c1989f03fd9cda5dfdcd5f499`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`6fea6f08183d913d7641429df7d85f78625cf0ce916abe07ffa72bd1875148eb`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/agent_outputs/source_contract.json` (`b3f5b6c9977098a2e48e38e569ce92daf6641300099fc1f8bb6329eb57ce881d`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/decision.json` (`3aae32d29e647c1ff0a399ba61a7c6ecd9978eceb9e06164de8bae0f71bb1974`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/agent_outputs/adjudicator.json` (`3025456eff60a9c9af18c6c1f9421d7be4d0ebde73e0cbf181457e53eddb6af6`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/agent_outputs/blind_translation.json` (`e104660039d3b031f903f515e8f7296fde48c853ca781817491cbf15b54902a9`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/agent_outputs/direct_judge.json` (`8eba7e89c400fdc521b17b82cbbb8b4a9f18019b1648440344a5821aadb01d0e`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/agent_outputs/paper_source_contract.json` (`cc856c94ce22bcb89d018b431db65cfb6c20d25df7bb6aaeb660c48c42f5c886`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/agent_outputs/roundtrip_judge.json` (`3d42a123faab7da7fb94e3706528e9e493c1bf3989a722611ec9157adfd3d770`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/agent_outputs/source_contract.json` (`cae96a861777731d67ac9ede8d9bc2817755f7ed2ee01592e13d0cfbd8f9dc70`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/decision.json` (`a9f3751fafb151aea9974a1e88cc94c4e6f0a4a2f7f5d6fb024c0462c5c601e1`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/blind_dependency_inventory.json` (`0f77a178b783d81dd3d4e10f286135cb7e3daa777bf968f3a643c7b985e240d7`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/blind_dossier.md` (`594676c557447428fa04d3999eb96b85169e0039cd6882467b539ffe7cb8fe48`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/blind_review_packet.md` (`594676c557447428fa04d3999eb96b85169e0039cd6882467b539ffe7cb8fe48`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/declaration_dossier.md` (`60a799365b1773519458d839c1ee04d267ddfb309acbea6ae400e8365e3a14e0`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/dependency_inventory.json` (`2749561c9343fb18101cd6f4dc1c9029ff9d100be9a6ee78b66f47ebd722ee4d`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/dependency_reuse_direct.json` (`acb3838c216564c282ba4e3e4487840de14d506f28f7b10501c4ffe625ca5064`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/direct_review_packet.md` (`4d621852b9a906d1bafa361b163ab305a87c034b648cac359603affbdbac66ad`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/paper_source_locator.json` (`29399d42dec8e4d771178436cda1303a77490d8820b032eb370ddffe5e202bd7`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/source_locator.json` (`d1ae628acc118c8d298e3add396694d62b669089f91e02000ae0d849f48bade6`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/agent_outputs/adjudicator.json` (`5846938a59bd31bd2136cecb5de74d9d860f666e2e0f1a8c72f62270658eb0f4`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/agent_outputs/blind_translation.json` (`0bd6e5ca9d407db6a7059d88640098aa305a3468c80df1c65ac0f20f805c6f4c`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/agent_outputs/direct_judge.json` (`00fbbfd091f8311e375fab9bb8d0a3bf31dd0efc1ceb657330cbba658d82272d`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/agent_outputs/roundtrip_judge.json` (`a11a107ed4394d1a3acdb124867d42cdbe04bfe1d89733a7d846f39bdd9819e6`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/agent_outputs/source_contract.json` (`0aacd322891b6156deaab73e5155df812157665e0916cbbad007330470c048e9`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/decision.json` (`ec2a8cf7775648da503ea6e74b2d9e57f06acabd26c5d0e462adfce849a1c2b5`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/inputs/blind_dependency_inventory.json` (`b6bc214f974565af989b50884268797ea4e3dbde928ee63e3f3860c5f3c0cde9`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/inputs/blind_dossier.md` (`6fe713ab7c72ecb9e9d96cfd28523943aac19a7dea1e011c6641c908ee9ed56e`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/inputs/blind_review_packet.md` (`6fe713ab7c72ecb9e9d96cfd28523943aac19a7dea1e011c6641c908ee9ed56e`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/inputs/declaration_dossier.md` (`3e8dc6ae9aa80638d51d67a6a5840d6e164eeae5a3cd002228c4900381513434`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/inputs/dependency_inventory.json` (`d2d487d1aa68942f4fb13d4862bab45ad02feda6ecd70f4e1f197563478e40d9`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/inputs/direct_review_packet.md` (`e3172064dd23626fc0f280a01ae29a21fc2f463c053dfcde702bf9cc29e57043`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260821T232904Z/inputs/source_locator.json` (`dc203ccec366dac29723aa263699667cf7ecd81e9f076407eea37d3d5e6531f8`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260822T123318Z/agent_outputs/adjudicator.json` (`59b3d40f8c979408ef74737e590b00458845eedc90294fea79f452f5b3cf116a`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260822T123318Z/agent_outputs/blind_translation.json` (`0302a2133f6ba47e05d1cddf06747a3fc64395b8649528a0370b1e737955d055`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260822T123318Z/agent_outputs/direct_judge.json` (`3b6fa31131fb774d67a410c3c0afbbc21a2a7a473a33dbecebce4a73a78c6e0b`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260822T123318Z/agent_outputs/roundtrip_judge.json` (`f325390cdacf499eb37db570bfaf641f3192624b2d1129423a5c6a539cf052b5`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260822T123318Z/agent_outputs/source_contract.json` (`81f0f614d32ecad5910df2533a4940cfbe00fc95aa305b50eb88a9c212dd017e`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260822T123318Z/decision.json` (`acffcbdafeaf971bca127bba11fd1c0847e80606e72ccb7321c1ddecb4be76db`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260822T123318Z/inputs/blind_dependency_inventory.json` (`f2d7d97ed31fc536cd84d1b64e7c1c7fb6a2d1cdcf6b77c0832259c45a930c93`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260822T123318Z/inputs/blind_dossier.md` (`10a8d521f62b1160edfdd78281ecefa832872c0a7f393d0ce0455974807d8a6d`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260822T123318Z/inputs/blind_review_packet.md` (`10a8d521f62b1160edfdd78281ecefa832872c0a7f393d0ce0455974807d8a6d`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260822T123318Z/inputs/declaration_dossier.md` (`4b85d00c9731dda68c557a780f854884b530c043a1f11a33b25fb483f252c80f`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260822T123318Z/inputs/dependency_inventory.json` (`b31c84d0900d34eab4272b5c1862c1b4276bbdc7bdcfd8260c90606f8b2bb4db`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260822T123318Z/inputs/direct_review_packet.md` (`1d8e110b368d53c16adee87f55951c4f40caad12503d632987f7a76ad729fac1`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260822T123318Z/inputs/source_locator.json` (`dc203ccec366dac29723aa263699667cf7ecd81e9f076407eea37d3d5e6531f8`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/blind_dependency_inventory.json` (`9c8977df3e81621f35e4a05d67eb1a3056c99e0bfae0e09a38d3a690ea2c6b7b`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/blind_dossier.md` (`64fb09ac34006d8c160a77cd176f146a0485afa6768c240372c599de5ee3636e`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/blind_review_packet.md` (`64fb09ac34006d8c160a77cd176f146a0485afa6768c240372c599de5ee3636e`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/declaration_dossier.md` (`44ec8d57d5692b77ad215be74efbec3c1b9bd9184355b72f112588ad14381acc`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/dependency_inventory.json` (`d70deb43bd948b2fe1c57c3846f5f10c0649b1a90bdd0ec32b04ddebd4df37bb`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/direct_review_packet.md` (`eb3ea8e89bd34869fdcf5b6d07a5308c0fb474fae4653f8f0961be5b815c57e4`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/source_locator.json` (`dc203ccec366dac29723aa263699667cf7ecd81e9f076407eea37d3d5e6531f8`)
