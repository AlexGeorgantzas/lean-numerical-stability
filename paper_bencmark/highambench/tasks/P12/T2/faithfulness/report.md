# Faithfulness audit: P12-T2

- Classification: `faithful-equivalent`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `1b581058811f544b9aa568725c1f1d163124a9c0b4fb7685d039254c1b9c8411`
- Paper SHA-256: `0569d969cebaabe42de69fef10fa91002af12d62149af7485d0712414b53c2a1`

## Decision

The declaration reproduces the paper's arbitrary-radix finite-real format, existential representation exponent, exact equation (7) threshold, nearest first operation, faithful subtraction operations, and three-step FastTwoSum execution. The local no-overflow wording attached to implication (8) does not modify Theorem 2's expressly stated hypothesis list. The proof itself presents both subtraction equalities as steps of Theorem 2, and the additional nearest error bound follows directly from the source definition. Both implication directions therefore hold, the proposition is nonvacuous, and the appropriate classification is faithful-equivalent.

## Implications

- **Lean implies paper:** `yes`. Under paper-matching format, representation, magnitude, and execution hypotheses, the declaration directly concludes s+e=x+y, while the execution relation identifies s as the nearest-rounded x+y. This is equation (3).
- **Paper implies lean:** `yes`. Theorem 2 gives equation (3), and its proof explicitly establishes t=s-x and e=y-t under the same hypotheses. Nearest addition and representability of x independently give |s-(x+y)|<=|y|. Equation (8)'s local qualification does not add a premise absent from Theorem 2's statement.

## Findings

- **note / overflow qualification:** This is a proof-exposition caveat, not a declaration mismatch. The result must not be reinterpreted as specifying IEEE infinity or NaN behavior.
- **note / ceiling encoding:** Equation (7)'s coefficient, ceiling placement, non-strict boundary, and scaling are preserved exactly.
- **note / explicit proof consequences:** These conjuncts do not make the declaration semantically different or merely reduce applicability; they are nonvacuous consequences under the same hypotheses.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `pass` |
| `S04` | `pass` | `unclear` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `unclear` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `not-applicable` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `71` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `71` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/agent_outputs/adjudicator.json` (`dbb8dbab8af334832c123cfa693e5e81d6146c0f7a527b11c57ece115d85b530`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/agent_outputs/blind_translation.json` (`ef86fa99c6f60fbc3939e43df6180f461eafbbf30f2870a106e0ffdc8f48df5d`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/agent_outputs/direct_judge.json` (`40c71ba5b137a0a32d1262bbefc23c78ac3c77e9e9c7345b985e40fa86ac080b`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`34873a74bff530e359c1928c358ec7fc859c6d7e0f04e0ab7fbb64bb5fcb4240`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/agent_outputs/source_contract.json` (`33903f35697265864eec5229b7efef50eab9b232dbe1770c80bb6b7d006bd9b7`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/decision.json` (`b3aaecee4eeeee7b7a3636d6e0f05b5eca68dfd5ba7ea367fecea1a079cc6b94`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260815T083155Z/agent_outputs/blind_translation.json` (`4d5cbece83c6f5d97976986f4d37894cd76e57ad76a04f85282db04f87d8ef30`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260815T083155Z/agent_outputs/direct_judge.json` (`dfaf65b1701caa07f898a1e191aa701a4ca7ede77b3f593dc30e1cd0e49b546d`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260815T083155Z/agent_outputs/paper_source_contract.json` (`c14eaa2ba1c25d2284fb972ef8a21fb4aa3b9f4953061dea7bb0ea5b382a6321`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260815T083155Z/agent_outputs/roundtrip_judge.json` (`6fba70776af23ad14e4c57649165551e73cdb87d0f92bbe61cfe92ba8c9341ea`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260815T083155Z/agent_outputs/source_contract.json` (`47144455f1f2ed0ce9e54c6f8e0d30526465d81d5686bbff28b50ff2075f0dcc`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260815T083155Z/decision.json` (`9aedb858bc88697db6c7378d736823d03b3483d3aaea913c410868e5a7ca5cbe`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260815T083155Z/inputs/blind_dependency_inventory.json` (`4f6061cda5daf81866ddde25ac898c1e418320e376eabe39461828d83e13be41`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260815T083155Z/inputs/blind_dossier.md` (`2f81ddc7f6915ee4e168a1b1e3ef4258a7587ebe12f1ce1e3287b3e69e545d0b`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260815T083155Z/inputs/blind_review_packet.md` (`2f81ddc7f6915ee4e168a1b1e3ef4258a7587ebe12f1ce1e3287b3e69e545d0b`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260815T083155Z/inputs/declaration_dossier.md` (`ce68f7d8494fb5b1c1175de6b201ddd63c5a3e7ca2863b1a3ec47c9277102309`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260815T083155Z/inputs/dependency_inventory.json` (`0b95e5fa47a5243f0803a420e6e1044294160fc42f6ce8435ad37028aafb4644`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260815T083155Z/inputs/dependency_reuse_direct.json` (`559df889b80af0c4ee1618bbfd62c39e146443164b272c67313338a3398b47c8`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260815T083155Z/inputs/direct_review_packet.md` (`8b5adc1e7aa2b4d2360a1ed6d3a619a8f12af0e6402e1f726c502e6ce2f966e6`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260815T083155Z/inputs/paper_source_locator.json` (`515de0f8e7e7ece14b209a55702074a38799c848bbb9eb747b29a9993464642f`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260815T083155Z/inputs/source_locator.json` (`f956480b09f86c030e7fd95f06f82ef07a23bd04ae6be5c2c9114d90cc0e7581`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260821T212229Z/agent_outputs/adjudicator.json` (`f666fcaf73ba493857054c288d7837b9ceed543118432f88d4fea39f9152b3b2`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260821T212229Z/agent_outputs/blind_translation.json` (`7893e6ed9cda7453e65ea06ec0285e91ac56e083e5ff660fccb796f0466f9569`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260821T212229Z/agent_outputs/direct_judge.json` (`736eca830194efed341b2f477e70066ee4291b707907eba724798b4417505acc`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260821T212229Z/agent_outputs/roundtrip_judge.json` (`3dd8704a681f97097bc97a5a53983df5fb7bbdd002fb8fd7d8964bef78e65cd6`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260821T212229Z/agent_outputs/source_contract.json` (`00b4cd660cea1882f6210e3b6cfa5a6aa80b8b2c706ed65640d369726a32c714`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260821T212229Z/decision.json` (`7eab82a0154ca3f46f0c18c8496a23f60f7d50025f553b3861fbbce63e02fba9`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260821T212229Z/inputs/blind_dependency_inventory.json` (`2410d057619226a3986834d8d9c608ad2b4dda3db7dc9737801f694b955c9fe6`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260821T212229Z/inputs/blind_dossier.md` (`b1b5a8881b75bbe43d8a06f8113bddab22ee7f419a36b7d5585f796da189ab00`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260821T212229Z/inputs/blind_review_packet.md` (`b1b5a8881b75bbe43d8a06f8113bddab22ee7f419a36b7d5585f796da189ab00`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260821T212229Z/inputs/declaration_dossier.md` (`438c309d9cc3882be5d0d196d2d478263c4aad5141c1394a82da7f328b0133f3`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260821T212229Z/inputs/dependency_inventory.json` (`d3b590f34c537f3f855fcf2f840c8a75d8cf01f855085bf3a27610f77b5f84da`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260821T212229Z/inputs/direct_review_packet.md` (`8eb3747ad0d9b495345e4e45e478d005fb87f8c68343fa33182cb5012c6a7401`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/history/20260821T212229Z/inputs/source_locator.json` (`fc24596ad6e5733b8cd10a229c3f132f88fd6bde2c22712e909c76438015d12d`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/blind_dependency_inventory.json` (`c3d66f2d7f809e582fa71cdef5f13454bd08818eede474068ff9227b4ec0d531`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/blind_dossier.md` (`3dc6a8e08628657201e790a6ba3a003a045f987380991cd45b2cd34cbfa22894`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/blind_review_packet.md` (`3dc6a8e08628657201e790a6ba3a003a045f987380991cd45b2cd34cbfa22894`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/declaration_dossier.md` (`94bff0f14fde37c92ccbda1330994e7219b5096c6b62b6e7b8a3ed367e3cd533`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/dependency_inventory.json` (`ff811ab822b12f018915196359440242b56c8c83a75f3492baf0cd9cd054bd82`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/direct_review_packet.md` (`05348c659fb899329ada3990fc7fb269e8fb70bbc14fab1c0d7eed08ea55350c`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/source_locator.json` (`fc24596ad6e5733b8cd10a229c3f132f88fd6bde2c22712e909c76438015d12d`)
