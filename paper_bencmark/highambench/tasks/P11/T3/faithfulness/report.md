# Faithfulness audit: P11-T3

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `false`
- Target SHA-256: `a7c13485b8f32f7701cce22d1839e454af8a5ff237d253a3bd6c7fedfa6d2077`
- Paper SHA-256: `72b7521848be07971a6721ea0356bb898c63e21b8ad3aa109fee8f41517284a5`

## Decision

The target faithfully represents numbered equation (7): it uses the operator 2-norm of I-Q_k^TQ_k, the exact c4 coefficient, the square of the inverse-based condition number of the computed leading R block, and one-based prefixes k=1,...,n. The family and run structures preserve the full-rank real rectangular setup and specifically trace Algorithm 2's pythagorean diagonal. Equations (4)-(6) appear in the residual-asymptotics argument in precisely the roles used by the appendix. The main difference is deliberate strengthening: the paper suppresses O(epsilonM^2), whereas Lean supplies a uniform radius and explicit quadratic remainder coefficient. Therefore Lean implies the selected paper conclusion under its first-order convention, but the displayed paper statement does not entail the exact formal remainder package.

## Implications

- **Lean implies paper:** `yes`. For every formal instance representing the paper's successful normalized CGS-P computation and upstream estimates, the exact Lean inequality has the same leading term as equation (7) and an explicit coefficient times epsilonM^2. Suppressing that term under the paper's stated first-order convention yields equation (7).
- **Paper implies lean:** `no`. The paper states only an unspecified O(epsilonM^2) qualification and does not itself provide the particular uniform radii, residual coefficients, norm bounds, or explicit quadratic coefficient required by the exact Lean inequality. Its appendix motivates these witnesses but the displayed result alone does not entail their concrete formal package.

## Findings

- **note / explicit-higher-order-refinement:** Lean implies the selected first-order paper result, but the paper statement does not directly imply this particular exact remainder bound.
- **note / selected-conclusion-modularization:** This is complete for the equation-(7) task but is not a single declaration proving all five conclusions of Theorem 1.
- **note / floating-point-abstraction:** The formal theorem applies to a broader class of compliant arithmetic models while still covering the paper's intended normalized computations.
- **note / explicit-second-order-strengthening:** The translation recovers the paper's selected result but is not implied by the paper's displayed first-order statement, so it is faithful-stronger rather than equivalent.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `pass` |
| `S04` | `pass` | `pass` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `pass` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `143` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `143` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/agent_outputs/blind_translation.json` (`4ea26bab7407661393e7d5df278ba9e0a23481f4f8aa346359450cf4f975a7cf`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/agent_outputs/direct_judge.json` (`d18314c176067f0f657f613460fd88b35622ff1d08b2e45b55d1fe27f01fdfb8`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`0a9fe6a13450735956e33b67dac34bc3e5a5979b51a01c2d1dd4458aa14ea9a1`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/agent_outputs/source_contract.json` (`d5940b5059927840bc38c6605b532819486059fcd87fc89cf9a6f478f3410ce1`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/decision.json` (`ca0feb7f9d47f9c365066cff57241c25fa8d2b852e86e51fb65e00a78d199a80`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260815T081207Z/agent_outputs/adjudicator.json` (`f5e3c756e8e7b98057f8beed5b509c462ac564d8db18fecf6a1b0b02c05ba79c`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260815T081207Z/agent_outputs/blind_translation.json` (`8c6a3b0d929496a8d39edc63dea1b0fc258b291d951c5917f916013cc7ccafa0`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260815T081207Z/agent_outputs/direct_judge.json` (`a9e043560225a247eb60eb11df7b668eea45bc5d4923976ea9b07cf4bfdc13c8`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260815T081207Z/agent_outputs/roundtrip_judge.json` (`56e4467deaf61d214633ea7a6f4f293a7428c07bc78f7bc456219a2002a2f826`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260815T081207Z/agent_outputs/source_contract.json` (`194111c880ac26678dbfdb7b61d1e11b2b3bff2fac14b933d761ec649f8f5452`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260815T081207Z/decision.json` (`3187a62a92ae74923194e5c4bfee972f15229d302f8858805f8ce521a576c0a9`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260815T081207Z/inputs/blind_dossier.md` (`659d69cfdf03fdb38dde10997ba8ab55d5fa1b7f24ee649e3248597c04417b67`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260815T081207Z/inputs/declaration_dossier.md` (`e9b1a1ae64a6e5396574b5b2009bb11d9338b209b1b8e60de0e1eae9b6bab8ae`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260815T081207Z/inputs/source_locator.json` (`d24934d1efaca21f42feeb65395e13f8827a6f1ddca53a9e5b45136a330a11f4`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260821T205703Z/agent_outputs/blind_translation.json` (`d394f63263058025e9cee598f5579d034e6c71021cd79baa353d920bfcbdca49`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260821T205703Z/agent_outputs/direct_judge.json` (`a31fbb6dc1dd588fc79fac87f1d7dde429088ee6580df9390fb4dff8d7dacca9`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260821T205703Z/agent_outputs/roundtrip_judge.json` (`953165a95ea6bb4309976bee92d0f1433642008d7b7bce0d1bdde3f99d9a5a8c`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260821T205703Z/agent_outputs/source_contract.json` (`47e65a65f2c17dd755dbc441bc82dbfdca1fdb2de79b21ff21ea5971edd8516b`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260821T205703Z/decision.json` (`921f6a7a0e8e580f7e53e755321f690fa2d82932dadb47f27a9643df39eaf1d2`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260821T205703Z/inputs/blind_dependency_inventory.json` (`a68c90ccbc94fb63ddf2908f73babd5a653b0b512c6d64433a266eb0d3ad6c2e`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260821T205703Z/inputs/blind_dossier.md` (`661c9a60c9ec4ac226429c7ee2182b7e389710f9134ab271c657dcb698978ccc`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260821T205703Z/inputs/blind_review_packet.md` (`661c9a60c9ec4ac226429c7ee2182b7e389710f9134ab271c657dcb698978ccc`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260821T205703Z/inputs/declaration_dossier.md` (`2e5897fdfeb98a5173677a84f05f628aca74356c2ecdd5012003470fd7bdba19`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260821T205703Z/inputs/dependency_inventory.json` (`bb4a46bccc95e435c421e057bc927a0cb18320deaf6a2245de9c0bde34c8d288`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260821T205703Z/inputs/direct_review_packet.md` (`215ca35c06a41ff1a2dc709c845314979a20b099ee638826967dfa273e064074`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260821T205703Z/inputs/source_locator.json` (`462bb0ce8a8f57893759800327728a43d0213f88c39ae9c5db657ef92813e402`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/blind_dependency_inventory.json` (`a1e882e2ed79466783af96690b24574177457c8d5d1900efea4e8632d8d6750d`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/blind_dossier.md` (`d8d6091a491a4931a5560c2d56f69d6bd46b7a8d23eabd3b7832cffc595d5bf3`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/blind_review_packet.md` (`d8d6091a491a4931a5560c2d56f69d6bd46b7a8d23eabd3b7832cffc595d5bf3`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/declaration_dossier.md` (`1cfe2e4ce46fa6b5b11003d7f44354da818491b22c701deaae859752643f898b`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/dependency_inventory.json` (`c70cbdea0326dd64c675d82ce4bd0f8d8aa65b2bc22523f617a0549fc62b1678`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/direct_review_packet.md` (`d2956c81c97f3513bbffdee2b6cc67aa63f5689951752b7d59221416d50ad8a4`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/source_locator.json` (`42d94e4ce965d0b75d9238029075bc915cb497b162989a889bca91dfd351bd77`)
