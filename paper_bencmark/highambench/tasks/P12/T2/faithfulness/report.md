# Faithfulness audit: P12-T2

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `3100033c4f50b31b8a19dc91b1cd9d58aec379619098437b917b98d9b7e560c1`
- Paper SHA-256: `0569d969cebaabe42de69fef10fa91002af12d62149af7485d0712414b53c2a1`

## Decision

Primary PDF evidence resolves both unclear checklist items. The Lean model has substantive admissible executions, so S16 passes. S11 fails because the execution predicate undeniably adds a no-overflow requirement for the initial addition, despite Theorem 2 having no such premise; uncertainty remains only about how the paper intended the subtraction-specific overflow qualification. Independently, omission of the ceiling in condition (7) excludes nontrivial odd-radix source cases. The paper result therefore entails the Lean target on its restricted domain, while the Lean target does not recover the paper theorem's full domain.

## Implications

- **Lean implies paper:** `no`. The Lean theorem covers only a proper subset of the source domain. For beta=3, p=1, exponent range 0 through 1, and x=y=2 represented at exponent 0, the paper permits |y|=2 because ceil(3-3/2)=2, while Lean requires |y|<=3/2. The source execution s=3, t=1, e=1 is nontrivial and satisfies exact reconstruction. Separately, beta=2, p=2, emin=emax=0, x=y=3 isolates a source case excluded only by Lean's addition noOverflow premise.
- **Paper implies lean:** `yes`. The unceiled Lean bound implies the paper's ceiled bound because beta^e is positive, and Lean assumes nearest addition, faithful subtraction, and additional range conditions. On this narrower domain, Theorem 2 and its proof yield t=s-x, e=y-t, and s+e=x+y. Nearest addition also gives |s-(x+y)|<=|y| by using representable x as a candidate.

## Findings

- **major / condition-7-ceiling:** Every odd radix loses valid boundary cases. For beta=3 and p=1, the source coefficient is 2 while the Lean coefficient is 3/2.
- **major / extra-overflow-hypotheses:** The target excludes source executions such as beta=2, p=2, emin=emax=0, x=y=3, where nearest saturation followed by exact subtractions satisfies the paper conclusion but |x+y|<beta^p beta^emax is false.
- **note / nonvacuity-and-extra-conclusions:** The target is globally nonvacuous, but its extra conjuncts are source-supported consequences rather than genuine theorem strengthening that could offset its narrower applicability.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `pass` |
| `S04` | `fail` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `fail` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `not-applicable` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `unclear` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `pass` |
| `S16` | `pass` | `unclear` |

## Dependency coverage

- Blind translator covered `72` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `72` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D008, D013, D021`.

## Remaining uncertainties

- The paper does not separately define overflow or state whether the qualification preceding equation (8) is an omitted global side condition. Primary evidence therefore does not determine whether Lean's first_sub_no_overflow and second_sub_no_overflow predicates are exact intended formalizations of that qualification. This does not affect the classification: add_no_overflow is independently unsupported, and the missing ceiling independently narrows condition (7).

## Audit artifacts

- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/agent_outputs/adjudicator.json` (`f666fcaf73ba493857054c288d7837b9ceed543118432f88d4fea39f9152b3b2`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/agent_outputs/blind_translation.json` (`7893e6ed9cda7453e65ea06ec0285e91ac56e083e5ff660fccb796f0466f9569`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/agent_outputs/direct_judge.json` (`736eca830194efed341b2f477e70066ee4291b707907eba724798b4417505acc`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`3dd8704a681f97097bc97a5a53983df5fb7bbdd002fb8fd7d8964bef78e65cd6`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/agent_outputs/source_contract.json` (`00b4cd660cea1882f6210e3b6cfa5a6aa80b8b2c706ed65640d369726a32c714`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/decision.json` (`7eab82a0154ca3f46f0c18c8496a23f60f7d50025f553b3861fbbce63e02fba9`)
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
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/blind_dependency_inventory.json` (`2410d057619226a3986834d8d9c608ad2b4dda3db7dc9737801f694b955c9fe6`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/blind_dossier.md` (`b1b5a8881b75bbe43d8a06f8113bddab22ee7f419a36b7d5585f796da189ab00`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/blind_review_packet.md` (`b1b5a8881b75bbe43d8a06f8113bddab22ee7f419a36b7d5585f796da189ab00`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/declaration_dossier.md` (`438c309d9cc3882be5d0d196d2d478263c4aad5141c1394a82da7f328b0133f3`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/dependency_inventory.json` (`d3b590f34c537f3f855fcf2f840c8a75d8cf01f855085bf3a27610f77b5f84da`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/direct_review_packet.md` (`8eb3747ad0d9b495345e4e45e478d005fb87f8c68343fa33182cb5012c6a7401`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/source_locator.json` (`fc24596ad6e5733b8cd10a229c3f132f88fd6bde2c22712e909c76438015d12d`)
