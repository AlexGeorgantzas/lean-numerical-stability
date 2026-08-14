# Faithfulness audit: P04-T3

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `0e18f38681cc3b6f670c6dffe237b8b91b85bbd17f9212a2ca845ee8becc20e1`
- Paper SHA-256: `7ad9ebb7eef9864c58e9a3760ee308be48060647286f8e16cdc740ed4be5b862`

## Decision

The declaration is not equivalent to the paper's algorithm-specific statement because it abstracts away execution and admits additional precision configurations. Nevertheless, this abstraction retains the selected result without circularity: the run packages Theorem 4.3 and the triangular-solve certificates explicitly identified as the independent premises of Theorem 4.4's proof, while the final perturbation remains to be constructed. Every intended paper execution therefore instantiates the Lean theorem, and the run type has additional satisfiable instances outside the paper's operational domain. This is genuine nonvacuous strength, so faithful-stronger with accepted=true is the implication-consistent decision.

## Implications

- **Lean implies paper:** `yes`. Under the paper's context, a successful Algorithm 4.1 execution supplies the D015 factorization fields by Theorem 4.3, and the substitution analysis invoked in Theorem 4.4 supplies yHat, deltaL, deltaU, their equations, and gamma_n bounds. The selected u_FMA is stored directly as uFma. Applying the Lean theorem to that run gives exactly the paper's nearby-system equation and componentwise bound (4.7).
- **Paper implies lean:** `no`. Theorem 4.4 states its conclusion only for factors and solutions produced by Algorithm 4.1 and substitution under the paper's numerical model. It does not quantify over every abstract record satisfying the intermediate factorization and solve certificates, including records with no execution provenance or with uFma values outside the low/high choice.

## Findings

- **major / algorithm-linkage-abstraction:** The target is not an operational verification of Algorithm 4.1, but it is a broader certificate-level composition theorem from which Theorem 4.4 follows.
- **major / intermediate-results-as-premises:** The formal theorem measures the nontrivial algebraic composition step rather than deriving the intermediate numerical analyses.
- **minor / precision-domain-generalization:** All intended choices remain covered, and additional admissible certificate parameters make the theorem strictly more general.
- **note / conclusion-formula:** Once the certificate premises are fixed, the numerical conclusion matches Theorem 4.4 exactly.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `pass` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `fail` | `fail` |
| `S12` | `pass` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `81` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `81` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D007, D015`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/agent_outputs/adjudicator.json` (`2fd8132a78ec5026e8a2c9ca9736b763a573af56b497f1ecca92e2d918b7e6a0`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/agent_outputs/blind_translation.json` (`3fcbe8deae15fbb6f8bf8eeac8c571eb22ceea8bba82bfdfc5f110f614c6c2d8`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/agent_outputs/direct_judge.json` (`7d2bb8a7e872a19dce0bdc4b6262949ec9e809773089c3f9f78aac224bc5c28e`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`c164df24e57c5743d9ae7a10dc58706d990732e73266980bcc5a020690139b9c`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/agent_outputs/source_contract.json` (`455fa1a925ddd787334cb3be42236e8a471410ffedd5e58b511ae9fb71a89362`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/decision.json` (`1e4184228fb8c4d78881374668e2707bd0e5a90271d8f9aefde0f23f8dd8364c`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/history/20260814T155016Z/agent_outputs/blind_translation.json` (`30e59264b489cd97d3b85308b5345ca89ca297b2d3d103b345c6f96df813a5ee`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/history/20260814T155016Z/agent_outputs/direct_judge.json` (`8532745b82324ef46395f892209783f309a8c3eb4b58665ab2f32e276b6f8a69`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/history/20260814T155016Z/agent_outputs/paper_source_contract.json` (`f23d1d2864ab683fc44d7b4dd917ebb13c36417400d3ee09d7d5a642c3a0d785`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/history/20260814T155016Z/agent_outputs/roundtrip_judge.json` (`854a2cacf6df1f471885171b29aa604b403e2da488b28a295a9d1db0d10229cd`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/history/20260814T155016Z/agent_outputs/source_contract.json` (`0014aa4e845579171263aaeb595c2072db8a0d34e6d3ac7b10b022af11ff1bd3`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/history/20260814T155016Z/decision.json` (`41c992758dd02a47292939852b304c852267dc3502c425e661fd3e80b21541bb`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/history/20260814T155016Z/inputs/blind_dependency_inventory.json` (`4b94cfee5317878982f957321191b6c3d81d6ddee69428439e3413052fdd68c4`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/history/20260814T155016Z/inputs/blind_dossier.md` (`f1ab8ee76b928333543348e584f5e460ff81101249dc133bdfaa977fd78c6d3e`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/history/20260814T155016Z/inputs/blind_review_packet.md` (`f1ab8ee76b928333543348e584f5e460ff81101249dc133bdfaa977fd78c6d3e`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/history/20260814T155016Z/inputs/declaration_dossier.md` (`d5b7181c0887bed4460f8e3f547f18c6c48f94a5de1fd051fbdbc3162063dc10`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/history/20260814T155016Z/inputs/dependency_inventory.json` (`a5d04076ab452b00cc1417fad14fcf58d923ffc5e914a0146ab17d2141fc06b5`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/history/20260814T155016Z/inputs/dependency_reuse_direct.json` (`5dfec669146d909b31a5953df4213ce08063af744286ed5043aa8f1643d98e46`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/history/20260814T155016Z/inputs/direct_review_packet.md` (`fbeb16df8ad4b21006181f6f1eb103b56f73acf21a7260d75860286a8feba576`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/history/20260814T155016Z/inputs/paper_source_locator.json` (`609fbccbf417b9661d911f32e2ac6e1c09c3fa4c980c82c53b5c0edd480437f7`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/history/20260814T155016Z/inputs/source_locator.json` (`146919f1f2e368a94705a639e983d0247830330d80fc4e7582bbb63327a29738`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/inputs/blind_dependency_inventory.json` (`37b98fdfcb4f07d131afd71ef3290a674ac1ef53d2ffbbcc07083f781361caa8`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/inputs/blind_dossier.md` (`94cb7501ee14ab5aefd61b1b35aea284e373d32e2fda7e81537228d6e7478fc5`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/inputs/blind_review_packet.md` (`94cb7501ee14ab5aefd61b1b35aea284e373d32e2fda7e81537228d6e7478fc5`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/inputs/declaration_dossier.md` (`a2982fb1cb8f64bd77bbceb4df98517666118c12fedf93174dd38f8eaa35aa05`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/inputs/dependency_inventory.json` (`c5ce5e6533b5bd7483f029d54c1069f1882c6ee98c4bbacb70b08df2bdb9f499`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/inputs/direct_review_packet.md` (`835702c3484a3db0e023c47015fb59958db4b16475180684532939f590710de6`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/inputs/source_locator.json` (`c1e3e03f9ba1caf8640a7d8094359803a61e6d4b49f5b7e10f9b57e01e7afd91`)
