# Faithfulness audit: P07-T3

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `false`
- Target SHA-256: `9b7abd46008c2ebc9620c036bd3c8c5c79bc34a01f09ea42b8179b88f517614a`
- Paper SHA-256: `4c4d638b359719f47e2c4664a50e9fa8e4704e8b6b39923d73c41883a97c5790`

## Decision

The Lean declaration isolates and strengthens the exact algebraic core of Lemma 2.1. Under QA=Q_A, C=S Q_A, and T=R_A R^{-1}, its hypotheses are consequences of the paper's full-rank economized QR setting and QA*T is AP. The universal reciprocal correspondence of all two-sided Euclidean norm certificates determines reciprocal extremal singular values, so it yields the paper's exact kappa_2 equality. Conversely, the paper's stated result does not cover the Lean theorem's broader abstract domain or its certificate-level conclusion. This is a nonvacuous faithful generalization, so the correct classification is faithful-stronger.

## Implications

- **Lean implies paper:** `yes`. For a paper instance set C=S Q_A and T=R_A R^{-1}. The QR identities give AP=Q_A T, C*T=Q, isometries of Q_A and Q, and surjectivity of T. Applying the universally quantified certificate equivalence to attained extremal bounds in both directions yields sigma_min(C)=1/sigma_max(AP) and sigma_max(C)=1/sigma_min(AP), hence kappa_2(AP)=kappa_2(SQ_A).
- **Paper implies lean:** `no`. The paper result ranges over factors arising from A, S, and economized QR and states only equality of the optimal condition-number ratios. The Lean proposition additionally covers every abstract C,T satisfying C*T=Q, including nontriangular T and dimension configurations such as s>m that cannot satisfy the paper's row-independent-sketch regime, and asserts correspondence of every positive two-sided certificate.

## Findings

- **note / condition-number-encoding:** The target must be read as a universal certificate theorem. Under that reading it implies the exact condition-number identity; reading one fixed loose certificate in isolation would be insufficient.
- **note / abstract-generalization:** The declaration is broader than the displayed paper lemma and therefore the reverse implication fails, but the direct substitution C=S Q_A and T=R_A R^{-1} preserves the complete benchmark result.
- **note / dimension-extension:** These are additional cases outside the paper, not a narrowing of its domain; explicit positive-dimensional examples establish nonvacuity.
- **major / paper-specific binders and algorithm linkage omitted:** The reader must supply C = S*QA and T = RA*R^{-1} to connect the theorem to the paper, although that substitution is valid.
- **major / condition number represented indirectly:** Recovering the displayed paper result requires an additional extremal-bound argument, but the universally quantified translated conclusion is sufficient and strictly stronger.
- **minor / broadened dimensions and degenerate cases:** The translation includes trivial zero-dimensional and non-algorithmic instances not represented by the intended least-squares setting.
- **note / exact numerical and norm semantics preserved:** There is no rounding-model, probability, error-notion, or norm-kind mismatch.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `pass` | `fail` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `fail` |
| `S11` | `pass` | `pass` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `not-applicable` |
| `S14` | `pass` | `not-applicable` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `fail` |

## Dependency coverage

- Blind translator covered `40` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `40` dependencies (`21` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P07/T3/faithfulness/agent_outputs/blind_translation.json` (`242e338cd0de04d533169fab4bf7014835f463cbff0a0cc87fbe7596d94d51eb`)
- `paper_bencmark/highambench/tasks/P07/T3/faithfulness/agent_outputs/direct_judge.json` (`69c1be4a99b8e6ef6dbedc073853ba0567edaf859d1c60d8e7b70f24ea66005b`)
- `paper_bencmark/highambench/tasks/P07/T3/faithfulness/agent_outputs/paper_source_contract.json` (`822fe7aa06960deeaa078b8ac855714c9b957ac1656f37de3dcbbaa9f707f076`)
- `paper_bencmark/highambench/tasks/P07/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`08c802a2ee210d348fcfc1ad85a682ecee892c15a77f474c55d4f81fd3f6a5c2`)
- `paper_bencmark/highambench/tasks/P07/T3/faithfulness/agent_outputs/source_contract.json` (`2e46dca6a35bd46e8887f8c3d8ef4cdfb06ac38874108a554ca2d88080dddd7c`)
- `paper_bencmark/highambench/tasks/P07/T3/faithfulness/decision.json` (`3e4673a8e88d76bcedeb0187a3b15ea3564ff943f49ba4450e5b126e5812800a`)
- `paper_bencmark/highambench/tasks/P07/T3/faithfulness/inputs/blind_dependency_inventory.json` (`74ae34d79d419f1067f12832825f010d4bb792b39639ce0b6154af40e8f48828`)
- `paper_bencmark/highambench/tasks/P07/T3/faithfulness/inputs/blind_dossier.md` (`c7945c9f5c1cc6a16a0ac7aa65cf534711cf978ab9d3b90be22b24004d5d0d56`)
- `paper_bencmark/highambench/tasks/P07/T3/faithfulness/inputs/blind_review_packet.md` (`c7945c9f5c1cc6a16a0ac7aa65cf534711cf978ab9d3b90be22b24004d5d0d56`)
- `paper_bencmark/highambench/tasks/P07/T3/faithfulness/inputs/declaration_dossier.md` (`de4f47458d65f30a0aa6c21037c1edf3e9d34d8e38d5dea21c72bccbc26a5c75`)
- `paper_bencmark/highambench/tasks/P07/T3/faithfulness/inputs/dependency_inventory.json` (`6182a6d2e98c58fd87c842d335f874668b7ceb74c69305fcb165619c176c7535`)
- `paper_bencmark/highambench/tasks/P07/T3/faithfulness/inputs/dependency_reuse_direct.json` (`aa36aa6a2888758a90b0c9b90bb7ddbfd9c31499f0fd044c4ed223242c45c4d3`)
- `paper_bencmark/highambench/tasks/P07/T3/faithfulness/inputs/direct_review_packet.md` (`2171a26f15ffc2a2b8f577541d3a1dd86b81813b35e5c593c4472d2f5924ac11`)
- `paper_bencmark/highambench/tasks/P07/T3/faithfulness/inputs/paper_source_locator.json` (`7d16e3f6a7585561fffc335fcd99a77aec72a33a336198eca2c59fb9113440a2`)
- `paper_bencmark/highambench/tasks/P07/T3/faithfulness/inputs/source_locator.json` (`609cce6bbda034bc1eb8a7eb7cd81e09dee9113ba0ee3972b210923887599603`)
