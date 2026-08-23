# Faithfulness audit: P11-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `a7c13485b8f32f7701cce22d1839e454af8a5ff237d253a3bd6c7fedfa6d2077`
- Paper SHA-256: `72b7521848be07971a6721ea0356bb898c63e21b8ad3aa109fee8f41517284a5`

## Decision

The PDF confirms the intended CGS-P orthogonality bound, its full-rank rectangular context, condition (3), spectral norm, squared condition number, and first-order O(epsilon_M^2) qualification. The formal matrix and algorithm encodings largely match those features, and the explicit remainder is a reasonable big-O formalization. However, c1 is mis-parenthesized, making c4 wrong in the selected leading term and premise. The proposition also assumes uniform residual conclusions and auxiliary bounds over an epsilon family instead of deriving the paper's multi-part theorem from its stated hypotheses. These changes make the two propositions logically incomparable rather than equivalent, stronger, or merely weaker.

## Implications

- **Lean implies paper:** `no`. The Lean proposition only covers computations extendable to a uniform epsilon family with supplied exact residual asymptotics and auxiliary norm bounds. Moreover, its hidden condition uses the incorrectly smaller c4. It therefore does not establish the paper theorem for every Algorithm-2 computation satisfying the paper's hypotheses.
- **Paper implies lean:** `no`. The paper's bound uses the larger coefficient c4 formed with 2*sqrt(2)*m*k, so it cannot imply the target's smaller leading coefficient uniformly as epsilon tends to zero. The paper also does not supply the target's epsilon-indexed family, exact residual witnesses, or particular explicit remainder coefficient.

## Findings

- **critical / constant-definition:** For every admissible later column, the formal leading constant is generally strictly smaller than the paper's, changing both the hypothesis and selected conclusion.
- **major / hypothesis-conclusion-reversal:** The formal proposition assumes substantial content that the paper theorem proves and omits the remaining theorem conclusions, yielding a restricted derived lemma rather than Theorem 1.
- **major / quantifier-and-applicability:** Added uniform-family hypotheses exclude paper instances and cannot be counted as genuine theorem strength.
- **major / floating-point-model-linkage:** The formal algorithm trace can contain pythagorean operations unconstrained by its advertised rounding model; residual assumptions, rather than the execution model, must carry the theorem.
- **critical / constant-mistranslation:** Both the leading orthogonality coefficient and the strict smallness condition are changed, producing a substantially smaller first term for nontrivial dimensions.
- **critical / theorem-recast-as-conditional-propagation:** The core numerical-analysis content is assumed rather than established, narrowing the theorem to computations already equipped with the needed estimates.
- **major / missing-conclusions:** The translated proposition does not preserve the complete paper result.
- **major / higher-order-treatment:** The translation proves a different exact theorem under additional assumptions rather than preserving the source's first-order statement.
- **major / numerical-model-and-domain:** The class of computations and the quantifier scope differ in both broader and narrower directions, preventing either whole statement from implying the other.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `fail` |
| `S15` | `pass` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `143` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `143` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D002, D007, D008, D014, D015, D017, D018, D019, D020, D021, D026, D030, D051, D061`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/agent_outputs/blind_translation.json` (`c7b5d693a4500628d62df8a916505c292ed9dd8c98b98cd7a614a54cc5ef5603`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/agent_outputs/direct_judge.json` (`3921cd1b44edb064d9ed12361e4a9d0aaadde1746d72793393c08a2a7fdd23a9`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`8e4e292dd57ab10b64ba4fd0cce818b6f37336a31982fb01de8b795e41d1ca59`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/agent_outputs/source_contract.json` (`914758345fb1c46246bc04ac3f836a00673565e3a91e4399bffd9d03061b1a82`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/decision.json` (`089d79161dde848919beb03bfd9be498e38c677b7b005af58e04901c42f0cff5`)
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
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260823T133225Z/agent_outputs/blind_translation.json` (`4ea26bab7407661393e7d5df278ba9e0a23481f4f8aa346359450cf4f975a7cf`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260823T133225Z/agent_outputs/direct_judge.json` (`d18314c176067f0f657f613460fd88b35622ff1d08b2e45b55d1fe27f01fdfb8`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260823T133225Z/agent_outputs/roundtrip_judge.json` (`0a9fe6a13450735956e33b67dac34bc3e5a5979b51a01c2d1dd4458aa14ea9a1`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260823T133225Z/agent_outputs/source_contract.json` (`d5940b5059927840bc38c6605b532819486059fcd87fc89cf9a6f478f3410ce1`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260823T133225Z/decision.json` (`ca0feb7f9d47f9c365066cff57241c25fa8d2b852e86e51fb65e00a78d199a80`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260823T133225Z/inputs/blind_dependency_inventory.json` (`a1e882e2ed79466783af96690b24574177457c8d5d1900efea4e8632d8d6750d`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260823T133225Z/inputs/blind_dossier.md` (`d8d6091a491a4931a5560c2d56f69d6bd46b7a8d23eabd3b7832cffc595d5bf3`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260823T133225Z/inputs/blind_review_packet.md` (`d8d6091a491a4931a5560c2d56f69d6bd46b7a8d23eabd3b7832cffc595d5bf3`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260823T133225Z/inputs/declaration_dossier.md` (`1cfe2e4ce46fa6b5b11003d7f44354da818491b22c701deaae859752643f898b`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260823T133225Z/inputs/dependency_inventory.json` (`c70cbdea0326dd64c675d82ce4bd0f8d8aa65b2bc22523f617a0549fc62b1678`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260823T133225Z/inputs/direct_review_packet.md` (`d2956c81c97f3513bbffdee2b6cc67aa63f5689951752b7d59221416d50ad8a4`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260823T133225Z/inputs/source_locator.json` (`42d94e4ce965d0b75d9238029075bc915cb497b162989a889bca91dfd351bd77`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/blind_dependency_inventory.json` (`c9af3899302ca29a55ea21b259e788b5235a45b2da9d85a7153da1b0420c142e`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/blind_dossier.md` (`d303f49bf5e8b305ef4d49e817b77b69068aa49be6cb2355b34f97ed2518db59`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/blind_review_packet.md` (`d303f49bf5e8b305ef4d49e817b77b69068aa49be6cb2355b34f97ed2518db59`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/declaration_dossier.md` (`dfc2b49094f25598067df3a12d568a37169bff1aa27627a4c01cef28cf7a6a66`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/dependency_inventory.json` (`14ea7bcd2306779772d42578c27a5f283f45277e9413281da40ad48d77075cca`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/direct_review_packet.md` (`cd3ffa8aa06c074195dc24ee547d739b61ce95863a432d14cd7343be526c12c3`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/source_locator.json` (`42d94e4ce965d0b75d9238029075bc915cb497b162989a889bca91dfd351bd77`)
