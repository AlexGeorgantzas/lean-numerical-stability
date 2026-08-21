# Faithfulness audit: P13-T1

- Classification: `faithful-equivalent`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `d3c2d2f5f1b80abd0e6dd41f569a7299253fbef7d89a2c4b319ba69c31df4cbb`
- Paper SHA-256: `9ebf8adb699f96c82ccbb153dd6ca592c64475a8bc3e0703a50cb659b012c520`

## Decision

Primary PDF evidence and the complete declaration semantics establish the same exact real interpolation problem, componentwise perturbation model, relative output error, limiting supremum, closed-form condition number, and lower bound. The disputed finite bound and attainment are genuine consequences of the Lean domain and definitions, not independent assumptions missing from the proposition. The real scalar setting is supported by the paper's sign witness and surrounding floating-point context, while the right-sided limit merely formalizes epsilon's role as a perturbation radius. Both implication directions hold without reduced applicability or vacuity; for example, the one-node problem with nonzero data satisfies the hypotheses and has condition number 1.

## Implications

- **Lean implies paper:** `yes`. The first Lean conjunct identifies the positive-radius perturbation supremum with sum_j |ell_j f_j|/|p_f(x)|, and the second gives the lower bound 1. Unfolding D010, D014, and D015 yields the paper's finite inequality for every admissible perturbation. For epsilon > 0, the paper's sign-aligned Delta f is admissible and makes every nonzero summand have the same sign, so it attains the quotient. Thus all selected paper claims follow on the same nonzero-value domain.
- **Paper implies lean:** `yes`. The paper's n+1 distinct real nodes, data, and fixed evaluation point package directly into D001 and D007. Equation (2.1) agrees with D005, D006, D010, and D011. Definition 2.1, read through positive perturbation radii, agrees with D004 and D012-D015, while equation (2.2) gives D003 as its limit and proves 1 <= D003. The attainable sets are nonempty and bounded for positive epsilon, so Lean's totalized sSup fallback is irrelevant.

## Findings

- **note / derived-conclusions:** There is no semantic weakening, although separate Lean corollaries could make these consequences easier to discover.
- **note / source-sign-typo:** The typo affects neither the condition number, finite inequality, attaining magnitude, nor either implication direction.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `unclear` |
| `S03` | `pass` | `fail` |
| `S04` | `pass` | `unclear` |
| `S05` | `pass` | `fail` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `pass` |
| `S12` | `pass` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `unclear` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `69` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `69` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/agent_outputs/adjudicator.json` (`3de7adca88d8088f7dc80b697859150882f550f6c9f9cb08a4a10a102800bfdb`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/agent_outputs/blind_translation.json` (`0f0ef88ea15c446db9dcf02c4006515b7ff6061efafa867e8704aa3addbb6d10`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/agent_outputs/direct_judge.json` (`ed82cc5bb1a5553b296b486181ca7244c4b0579a0f3f0bb700ab0e8774790527`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`6560698e2ae73486f3ca5f647b5d91cd0909a32c1acc39f23104f32fd43fca54`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/agent_outputs/source_contract.json` (`ccb7699b7e42d99af53b23ac3717397f5a14c7221240fdcfb9da7614741cf89d`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/decision.json` (`2a8a825bbeeaf71d5e8b570cea4ac2d1a2f74b2af43e0c70649f74c710315410`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/history/20260821T095352Z/agent_outputs/adjudicator.json` (`8b4c80d79acc17d34ccf1f484dd7b284dc0efb5996ee01f2abfec4722d589b46`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/history/20260821T095352Z/agent_outputs/blind_translation.json` (`f388a6ceb3b2ef4963a9621ec489d775bdf564e51ff544f0c80f3a88c36599be`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/history/20260821T095352Z/agent_outputs/direct_judge.json` (`ce5c37f0a333fb2e4c581c8af5c1760897d63f3f8966dbcb593ab88609dadc00`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/history/20260821T095352Z/agent_outputs/paper_source_contract.json` (`0b665a5c91e976eec5d015b1b58ea8cec5aa3023d351689e493b8b019f9b8393`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/history/20260821T095352Z/agent_outputs/roundtrip_judge.json` (`1e75c100e88a5082ada5643b10759f74d1f3dbaedfce182fcee345602db67f18`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/history/20260821T095352Z/agent_outputs/source_contract.json` (`01737035b27887ac47bf9adfa541d023ce70271a101a5eac76bdccd160d1304f`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/history/20260821T095352Z/decision.json` (`6ea8121cb207ba6d546d5e30e964a78655eeb64323a56d75d9076e20ddd1e7e0`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/history/20260821T095352Z/inputs/blind_dependency_inventory.json` (`d648384163dd5cae777c1421fe58b2164efa2857c313fa103f7bbb41b8b7716b`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/history/20260821T095352Z/inputs/blind_dossier.md` (`b565729e119a95bb3180eff990e59dfef2876db46a0f9ec7bf1a0f54d19e1a4e`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/history/20260821T095352Z/inputs/blind_review_packet.md` (`b565729e119a95bb3180eff990e59dfef2876db46a0f9ec7bf1a0f54d19e1a4e`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/history/20260821T095352Z/inputs/declaration_dossier.md` (`7955bf90e349ac89b265190322972436709a5b97383ef901e8e001fc4db26e77`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/history/20260821T095352Z/inputs/dependency_inventory.json` (`3497ce0b70ebc4747f764d3e75800d4711c183dca27c9bd5f10abe92a6f39408`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/history/20260821T095352Z/inputs/direct_review_packet.md` (`731f7b5c3b812eef504dd38891a9b7ef8059677d83bf48c5171022ab615aa70b`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/history/20260821T095352Z/inputs/paper_source_locator.json` (`ec1d43325cb06b3c0839afb1c4848208a4c9dfd1b54b19aa5048fb5de3fa9f0f`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/history/20260821T095352Z/inputs/source_locator.json` (`6a5a07bd54eb34d3b14eec73c9ab60b51908b60fac71f167061bd961c3e3802d`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/inputs/blind_dependency_inventory.json` (`26c25333b6e36fac8f8a4ad8a4592d9ce802c626d75fabed2b2a36f39e58f5fb`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/inputs/blind_dossier.md` (`e98093e2ad4a7bc21868fefb4f24c7ad1c9d414b4879edfaf43f8d9c2f1946bc`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/inputs/blind_review_packet.md` (`e98093e2ad4a7bc21868fefb4f24c7ad1c9d414b4879edfaf43f8d9c2f1946bc`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/inputs/declaration_dossier.md` (`072e3e6a94ffbf4667f852a280a2a574d377a51918ed02f4f09ab51718c45ac5`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/inputs/dependency_inventory.json` (`1037ce2bd23674972adca73e1fa795596bd1db481a50e1fe2070bb8456941ce1`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/inputs/direct_review_packet.md` (`d36a463756830210791143020f5225b63d95e1d229d94ade2ea4c2bbc583b29d`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/inputs/source_locator.json` (`fd238cd08311ffdc11c5e35e1d5fcb6eccc79c32b796e348c709974a64cc6575`)
