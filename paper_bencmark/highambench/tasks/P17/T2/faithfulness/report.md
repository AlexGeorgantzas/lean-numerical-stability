# Faithfulness audit: P17-T2

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `false`
- Target SHA-256: `2a91b322f57d9538107713cf09209199c753850bdaee198795e77ae8f1cd56e4`
- Paper SHA-256: `df1ce5dd33285adfcffc6a4c7ab94f9604b46739cb848c6cbb5f997e8fac597d`

## Decision

After direct inspection of the cited PDF pages and the full dependency dossier, the target reproduces the exact relative absolute bias bound with kappa(a), gamma_{n-1}, and u_{p+r}; m is consistently the number of additions, so n=m+1. The finite expectation, recursive order, conditional-bias model, zero convention, and nonzero final sum all match the paper. The only substantive scope difference is favorable: Lean proves the same conclusion for every finite error process satisfying the sufficient model, not solely for Bernoulli SR_{p,r} implementations. Hence Lean implies the paper result, the paper statement does not imply the full generalized Lean proposition, and the correct classification is faithful-stronger.

## Implications

- **Lean implies paper:** `yes`. For a paper instance with n>=1, set m=n-1 and use the finite support of its n-1 Bernoulli SR decisions as Omega. Lemma 3.2, the pathwise bounds, and the zero convention provide the D011 fields, so the Lean conclusion specializes exactly to equation (4.6).
- **Paper implies lean:** `no`. The paper's stated Theorem 4.1 concerns actual SR_{p,r} executions. Lean quantifies additional finite error processes satisfying only the sufficient abstract bias model, including processes whose outcomes are not p-bit enclosing-value Bernoulli rounds. The paper statement alone does not assert the bound for that larger class.

## Findings

- **note / model-generalization:** The Lean result has a wider valid execution-model domain while retaining every paper instance, so it is faithfully stronger rather than merely equivalent.
- **note / implicit-nonzero-domain:** Lean makes the paper's necessary well-definedness condition explicit and excludes only the undefined zero-sum reading.
- **major / numerical-model-generalization:** The translated theorem applies to a strict superset of the paper's executions. Actual paper executions instantiate it, so this is a faithful strengthening rather than a weaker or different conclusion.
- **minor / truncation-linkage:** The translation does not reconstruct the concrete floating-point operation; T is largely auxiliary. This contributes to the strict abstraction but does not invalidate the bound.
- **note / nonzero-domain:** This makes the ordinary real-valued domain explicit and does not alter the meaningful cases of the paper statement.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `pass` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `75` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `75` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/agent_outputs/blind_translation.json` (`c6f424ea6793eef2fc16f8161c5fbc6198c9e78b3ba064ceced1a816d4caa523`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/agent_outputs/direct_judge.json` (`471dbc490a4b69f3c707355a31b90f941fc438c8ace4114eb8b1110e9c9a3541`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`ca1a1f8c89ddb9d7f849181c3c01ae410fe54e5c49ac167c757af13847d4ff44`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/agent_outputs/source_contract.json` (`339d6a1f0ac1b94329b6dd33cd6b0496c3e7215b8ad7b98d6141466f7fa9a9f1`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/decision.json` (`99441adcfc7cea165c44e4b8bdfdbc3c39f1f9ad800f987c7491b1300e40d106`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/history/20260820T164053Z/agent_outputs/blind_translation.json` (`6332c30f05ab15cb13ca46bb0a1d888b84841112b675e1eb38f76aa02899933e`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/history/20260820T164053Z/agent_outputs/direct_judge.json` (`00ae22fa556a524eaa9c821df0bb5408bb7656526520e8904c50685efa4ba25e`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/history/20260820T164053Z/agent_outputs/paper_source_contract.json` (`5856f4d88e51aeb1df8e36f051f77e90c96a2896bb707ed0186c2f74cf1ebc0b`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/history/20260820T164053Z/agent_outputs/roundtrip_judge.json` (`260448e421ebbac232ab700c392a78735e24930948120b491b6436170e4e4a55`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/history/20260820T164053Z/agent_outputs/source_contract.json` (`55db3e8fcc0a0f797e636c3a45c40f019c2835877bc94939b27e831b674a76a2`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/history/20260820T164053Z/decision.json` (`466c78f162e3db5cca4703be22cad1bfc630cfcf11db9f57d7c5c61274c5529d`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/history/20260820T164053Z/inputs/blind_dependency_inventory.json` (`dff0e8bf5222ec42cd8d87f3a6044ef897994e3b93903d5ede0438d523f98953`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/history/20260820T164053Z/inputs/blind_dossier.md` (`4eb2cc402bc41763a1b4108896fc4eb6855080cf71bc679ec5fd0ef665421610`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/history/20260820T164053Z/inputs/blind_review_packet.md` (`4eb2cc402bc41763a1b4108896fc4eb6855080cf71bc679ec5fd0ef665421610`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/history/20260820T164053Z/inputs/declaration_dossier.md` (`c2da7f09d1f7ec56c31208d2ecbe1762e47da908f2169dd61fe2fb403d0c7966`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/history/20260820T164053Z/inputs/dependency_inventory.json` (`a89493e0ffb03f26ac52608bad6cdf9e6cf86da04f500c282809b2ec6488d88f`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/history/20260820T164053Z/inputs/dependency_reuse_direct.json` (`90e88341c3bf5b33102d90da13363efc3287883e9f8c49d2b1b4df7ee53d8ea2`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/history/20260820T164053Z/inputs/direct_review_packet.md` (`5ff13a33521f8b3f9922a38183ea5dde74528edd5f222ab435b6c8e6d9980f19`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/history/20260820T164053Z/inputs/paper_source_locator.json` (`7b6e846a522a4293bd50e70522a875cdc8dd30515338efc2e70d99739bcb7161`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/history/20260820T164053Z/inputs/source_locator.json` (`35af6f2e55f21f175ca0eff099c1a2342351a4ac6bec953a58e9dec82662b60a`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/inputs/blind_dependency_inventory.json` (`f43dba575756cabd06479f93cb42c9725ae73edf7d950d25973d025396784964`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/inputs/blind_dossier.md` (`a82002a4b16de3d720b3d68e1a5b70cfa3584bf3e82edd1c1b04f2b34aac979d`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/inputs/blind_review_packet.md` (`a82002a4b16de3d720b3d68e1a5b70cfa3584bf3e82edd1c1b04f2b34aac979d`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/inputs/declaration_dossier.md` (`6157bab16d58fb74a2c920a0215091f223ab61362f38c6fa88d15ab9df590f83`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/inputs/dependency_inventory.json` (`4eeae640003b4b9478427021ce2bc842269e40ab70be176eb3293c496f81c065`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/inputs/direct_review_packet.md` (`5193411242693d04316eb204049b12487eb2d97d5828cf77faa67fbfd9b36db3`)
- `paper_bencmark/highambench/tasks/P17/T2/faithfulness/inputs/source_locator.json` (`35af6f2e55f21f175ca0eff099c1a2342351a4ac6bec953a58e9dec82662b60a`)
