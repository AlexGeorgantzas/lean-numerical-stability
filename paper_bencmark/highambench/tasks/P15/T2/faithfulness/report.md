# Faithfulness audit: P15-T2

- Classification: `faithful-equivalent`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `d67615e334bef3b3e171e89412ebcd25c97a86834c508d7be20d945d99bba8de`
- Paper SHA-256: `a5cb8eb779c1571f1549ea6838c7f2269302c960fb4ea21f8410060811270cd7`

## Decision

Primary evidence resolves the disagreement in favor of faithful equivalence. The paper itself crosses from scalar floating-point arithmetic to the matrix-vector backward-error interface in Lemma 2.1, and its proof of Lemma 3.1 begins from exactly the two stage certificates stored by the Lean execution record. The record preserves the fixed-right-hand-side dependence and ordered computation; it does not assume the aggregate perturbations or their bounds. The theorem constructs the same explicit DeltaAtilde and DeltaA, uses the exact Frobenius norm, gamma definition, cost b + r^(3/2), and mixed epsilon gamma_c beta term, and states both selected generic backward conclusions. Requiring this theorem itself to reconstruct the stage witnesses from scalar fl operations would collapse a legitimate source-level lemma boundary and is not necessary for statement faithfulness.

## Implications

- **Lean implies paper:** `yes`. Every source two-stage computation covered by equation (2.5) obtains the D022 stage certificates from Lemma 2.1, exactly as the paper does in (3.3) and (3.4). Encoding those certificates as a run and applying the Lean theorem yields explicit perturbations satisfying both selected paper conclusions (3.1) and (3.2).
- **Paper implies lean:** `yes`. For any admissible run, its fields instantiate (3.3), (3.4), orthonormality, and Atilde = A + E. The algebra on PDF page 6 constructs exactly D017 and D018 and proves both target bounds. The final target equality is ordinary distributive expansion of the exact coefficient in (3.2).

## Findings

- **note / abstraction boundary:** No floating-point-model faithfulness defect exists for this selected theorem; scalar-operation verification belongs to the supporting Lemma 2.1 layer.
- **note / precision wording:** The declaration must not be cited as a quantitative formalization of the later dominance prose, but equations (3.1) and (3.2) remain faithfully represented.
- **note / scope:** They are later specialization and corollary prose, not missing conclusions from the selected equations (3.1) and (3.2).

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `unclear` |
| `S03` | `pass` | `fail` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `fail` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `unclear` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `71` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `71` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

- The PDF does not quantify the phrase u safely smaller than epsilon, so no numerical equivalence between that phrase and the declaration's u < epsilon field can be established. This affects only the qualitative dominance and construction-roundoff interpretation, not the retained exact bounds.
- The PDF does not explicitly state whether the block dimension b may be zero. Lean's b = 0 cases are degenerate extensions and do not affect correspondence on the paper's ordinary dimension domain.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/agent_outputs/adjudicator.json` (`2ced5a04c62ba791db9306c75cad12ac9a00c79c798cff40baea74e9ce70cecf`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/agent_outputs/blind_translation.json` (`1eb449a82757820adc5d8558d2a5dc5a247bcf277ccb4f0bf410a1b4f5440719`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/agent_outputs/direct_judge.json` (`5017a8497d719b920e7ad42253661e8b7d241a93d8b52003d354aa827920b59f`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`ab032c68129ae95357a10a83d81e28b59f1518c8e26fd7468c6e34d90430f1d2`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/agent_outputs/source_contract.json` (`741e3f1163a52cdf09889149cdc2e0d9f89accf1017f7897c8cdbbb55471c2cf`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/decision.json` (`2bc916a26ef560653449dd0d6981a1655c86b117d7d42095c2bbca3c22be74eb`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/history/20260820T092610Z/agent_outputs/adjudicator.json` (`5ca4fba8baa7cba8447e8c4e5d17c8db37928281e651edc50e3666f834205e56`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/history/20260820T092610Z/agent_outputs/blind_translation.json` (`6513e9977d82f2fbf471fa04470e52c75ed30468725029cfd59b291203411832`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/history/20260820T092610Z/agent_outputs/direct_judge.json` (`398247ac5db9ed52e2576634b81f9bfdad23dc0e23ee3ac1d68d15971e2a2cb1`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/history/20260820T092610Z/agent_outputs/paper_source_contract.json` (`339fc5a797919c9e9bcd9c7d27d579722d8bfedc8091d16c4ab89148a1eb498f`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/history/20260820T092610Z/agent_outputs/roundtrip_judge.json` (`3228c035de2300f30ed94d6f55da524c66a6c6a78cff1caad1f91f39d13af79e`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/history/20260820T092610Z/agent_outputs/source_contract.json` (`4455adda22e4e4eadeba84ea892687d42f956eee3479e408c3ffa56573fe22fa`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/history/20260820T092610Z/decision.json` (`8735d55dec3dfa0ae3904265b689b82a8ba89ad37762492029528523c47a5c80`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/history/20260820T092610Z/inputs/blind_dependency_inventory.json` (`f5eb47df52a02b164230ef26cc5d661455ec5106992a2255f1d75a70de8278d9`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/history/20260820T092610Z/inputs/blind_dossier.md` (`6d8bb543f7578c2f1c488dbf291c9c900a371c9e1a260443e32703e75e307e7b`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/history/20260820T092610Z/inputs/blind_review_packet.md` (`6d8bb543f7578c2f1c488dbf291c9c900a371c9e1a260443e32703e75e307e7b`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/history/20260820T092610Z/inputs/declaration_dossier.md` (`438c7d18c1182e43d8bfd1edb7854f4e8ad8ff8fef9d4201c32b4980c510e0a5`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/history/20260820T092610Z/inputs/dependency_inventory.json` (`9c2d74cef085c58a341de6b05653f17efd313479c22ec2ceb313ce708cc2eb21`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/history/20260820T092610Z/inputs/dependency_reuse_direct.json` (`50929ce9988d93bf78236d3728964df2c9808bef33c0a86ca85716cff0244354`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/history/20260820T092610Z/inputs/direct_review_packet.md` (`3b30d3820cc27dbc331b4cebf11fc6a683bcd53528095602359a30f709d2e46e`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/history/20260820T092610Z/inputs/paper_source_locator.json` (`568b244880bf84912b78ba1130fd66ae2d43016e0a25f06e4510e3d731ee5223`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/history/20260820T092610Z/inputs/source_locator.json` (`7685e7e6f4cf635393f93721348220b99764d19b4ef32ad11b0d76f5d27ca76d`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/inputs/blind_dependency_inventory.json` (`3b585a2b3c9c798cdb4af4148e99f19f26ad3da9ed0815772e7bc8af26913bc2`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/inputs/blind_dossier.md` (`b3269791e0abca2e05f8cb568e14d3fcae72b8e81ce614b07987976c674f22c7`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/inputs/blind_review_packet.md` (`b3269791e0abca2e05f8cb568e14d3fcae72b8e81ce614b07987976c674f22c7`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/inputs/declaration_dossier.md` (`e11c6c011a05fb186dd0bc3678dec942bd405b8b509af3fc6b255476ab656e18`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/inputs/dependency_inventory.json` (`e92a0bf135680a785e7d634f3cd576a2c5949e1a23533e3d0ad4cd726ae1c434`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/inputs/direct_review_packet.md` (`93ef55e0534a58b594fa4137719861ecb9c821bd6ff3d14ce91a7c7ece773aed`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/inputs/source_locator.json` (`d2f256453438432ae72d5bc13b4d618ae4adfa5c930b5b39d38713a89607f87b`)
