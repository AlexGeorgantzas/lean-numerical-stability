# Faithfulness audit: P15-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `1877c9100346dbb2c098225c95b1e1eb7427985c008fc24996fa895785fc71e1`
- Paper SHA-256: `a5cb8eb779c1571f1549ea6838c7f2269302c960fb4ea21f8410060811270cd7`

## Decision

The declaration accurately preserves the final perturbed equation, Frobenius and Euclidean norms, c, gamma indices, all four xi values, both displayed remainders, and the exact perturbation compositions. Its unfolded execution domain is nevertheless different from the paper's: upper updates use the wrong predecessor cutoff, matrix triangular solves use a non-equivalent restricted relation, and one fixed-r all-precision family with prior bounds is required. These are substantive antecedent and algorithm changes, not genuine nonvacuous strengthening. Since neither statement entails the other, the correct classification is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. Using the Lean theorem to establish the paper theorem would require embedding every actual Algorithm 1 or 2 computation into the formal run type. The upper-row update in D067-D068/D088 uses j<i instead of j<k, the matrix solve certificates impose a special coefficient-perturbation form, and the run requires a fixed-r family over all admissible parameters. Thus the Lean statement does not cover the paper's execution domain.
- **Paper implies lean:** `no`. A formal run is not guaranteed to be an execution of Algorithm 1 or 2 because its upper update includes the current j=k product. Moreover, the paper's residual matrix-solve bounds do not imply the common coefficient perturbations required by D090-D091, and its pointwise theorem does not supply the declaration's all-parameter fixed-r family. The paper theorem therefore does not entail the Lean proposition.

## Findings

- **critical / algorithm-indexing:** The formal completion predicates do not denote either algorithm named by Theorem 4.5, which defeats both implications.
- **major / matrix-triangular-solve-model:** The formal relation is a restricted special case and can exclude valid paper executions; reduced applicability is not theorem strength.
- **major / quantifier-scope:** The declaration is a conditional family-level composition theorem rather than an equivalent formalization of the paper's pointwise algorithm theorem.
- **minor / precision-regime:** The exact admissible regime is not faithfully specified, although the source itself leaves the safety margin qualitative.
- **note / higher-order-and-vacuity:** The target neither omits the higher-order products nor succeeds merely by vacuity; these facts do not repair the execution-model mismatch.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `fail` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `fail` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `pass` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `unclear` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `unclear` |

## Dependency coverage

- Blind translator covered `179` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `179` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D017, D028, D044, D058, D059, D067, D068, D088, D090, D091`.

## Remaining uncertainties

- The PDF does not specify constants, signs, parameter dependence, or uniformity for O(u epsilon) and O(u^2), so reverse equivalence between the informal notation and the exact predicates D024-D025 is not textually determined.
- The paper gives no quantitative meaning for 'u safely smaller than epsilon', so the exact intended margin beyond u<epsilon cannot be recovered.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/agent_outputs/adjudicator.json` (`1db5cf5daed6ef402f69ae2ec6e2b917d762155738a883b394605edc8f9fbec3`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/agent_outputs/blind_translation.json` (`8e9855af311d2ac52a3f75a83d8b01c25446a2425e659d9faba590d7f987a230`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/agent_outputs/direct_judge.json` (`4bc64cd084f1ab210e9e6a86411918da7fe40e622281541ed0639b0171078b57`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`3228ffe7d5889f8a24d1463232cef0fd8966857ecddb773e30e53c220c833e71`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/agent_outputs/source_contract.json` (`9213a6b01080286137abb6d59adeddd784792868ccb883b1e732afe1457cc83d`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/decision.json` (`c278860550d35c000e8840062e47a1fd5b40ed1bfc55121c0c48b88ef3fe7671`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/agent_outputs/adjudicator.json` (`4311935f42a62715f3dd0c151b813d51499f63175f836c7cf819ee4d7c90c821`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/agent_outputs/blind_translation.json` (`e863d0a2062602a574fe83b7982e8cb51afd1623973ea809ba9781a983be50df`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/agent_outputs/direct_judge.json` (`6262e2541e9dce9111b21c18f3a8e2e5418fb00d7d291ebbce25212ae41584e2`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/agent_outputs/paper_source_contract.json` (`339fc5a797919c9e9bcd9c7d27d579722d8bfedc8091d16c4ab89148a1eb498f`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/agent_outputs/roundtrip_judge.json` (`41433addc668f60a98ced486313d98c95c0bc14478cd1bcfe473a9846f7f18ee`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/agent_outputs/source_contract.json` (`9fc7c9554b51771ef8f73ce95234a3e85825ebd2fa3c6fad39d07d445d6368f0`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/decision.json` (`1884fe900bd4baabf88cb07a38d7d37479ec61cbe33391b4b35a2c69e03f6d20`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/inputs/blind_dependency_inventory.json` (`9cbd2904499a9bf7a5f6d564ea389b8a451afef2ca9086f6e93901fffccc06ad`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/inputs/blind_dossier.md` (`ef6a30809f983a0f6286e7b06ab6be570eb28de78f6c5fed9d7abe84e9c978d8`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/inputs/blind_review_packet.md` (`ef6a30809f983a0f6286e7b06ab6be570eb28de78f6c5fed9d7abe84e9c978d8`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/inputs/declaration_dossier.md` (`c1b94f9ad0c0992839b78287f2ab5ec3b9996bb0006d7788dc24b703ae4ae305`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/inputs/dependency_inventory.json` (`2768c2c919d20cf047da9ebad2723933cd72b178b83c0650b0d2b10283fc5269`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/inputs/dependency_reuse_direct.json` (`fbd14dfd3917164bfad3b52631711d1545b15975bdf45dbe02e221108117986d`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/inputs/direct_review_packet.md` (`1aa029d06e8641698d1c9ffdfbcd36d4834c67e9b5cb58e49f0b65a77546ec59`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/inputs/paper_source_locator.json` (`568b244880bf84912b78ba1130fd66ae2d43016e0a25f06e4510e3d731ee5223`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/inputs/source_locator.json` (`244a38eb2c34a9f52dab5e2a1622b8ecf82862ab61fbf7d49c0853cf74e6fa2b`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260821T222418Z/agent_outputs/adjudicator.json` (`83573753cb17a6343c62420f253a9dd8ac32c952823dc96aca34020c9be2b696`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260821T222418Z/agent_outputs/blind_translation.json` (`e8cd65cffc379f33f37796d4fe48342972e1712ef6105129c612d2c52bb82e30`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260821T222418Z/agent_outputs/direct_judge.json` (`9c4b38e1bc1897bf4efa40787af8dafb092b359b77226bff69ecd0e9856b91e8`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260821T222418Z/agent_outputs/roundtrip_judge.json` (`51295d43d9e5cfc2f2abdf22c81dce8eaf6646592062d8ce7b39463a5c0eb6d7`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260821T222418Z/agent_outputs/source_contract.json` (`bf306c9ca6548f0195c3feec452bddea9b13de1de97e41bd15bc92bd48c011be`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260821T222418Z/decision.json` (`5a1fbca2bae1203639c7bf901901a80ed80ff9c00675dcf1884b7e0b31d9fc12`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260821T222418Z/inputs/blind_dependency_inventory.json` (`f08d73c1521737c2bbfea09bcbea9e22b9feff5636d15547f69b45d91b428832`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260821T222418Z/inputs/blind_dossier.md` (`1dea98e2d0e80563200aef63ab6d7ac7d67b0fa9592f9d3880b3afe17be8ae27`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260821T222418Z/inputs/blind_review_packet.md` (`1dea98e2d0e80563200aef63ab6d7ac7d67b0fa9592f9d3880b3afe17be8ae27`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260821T222418Z/inputs/declaration_dossier.md` (`23e3e6cc6d2cb70dd389ee98e879ae67cb70a4a68acfeb4c59c2fd4d720cd511`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260821T222418Z/inputs/dependency_inventory.json` (`df2f634f2b2be5672a237680e3d881e385fe247277ed4e4d1e6b6c5b5d6c72c3`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260821T222418Z/inputs/direct_review_packet.md` (`3e9fa8d12a987ed20d2037ce9938878d073305cd401bc8f479865b79d0eeaca3`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260821T222418Z/inputs/source_locator.json` (`a0e28441f60a8ba02cc844632b2dea2d670a1a5342b9244a70405225c82d9579`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260822T114236Z/agent_outputs/adjudicator.json` (`64809e84be6997be1ae45613d07c164cb4c45873c30be7650e8227cf811a1611`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260822T114236Z/agent_outputs/blind_translation.json` (`c043f821b67cf73d95d050c516eeed6429cd5f7c017ec3be845956a93f1ac053`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260822T114236Z/agent_outputs/direct_judge.json` (`cbee7ee1b7754ad97e3600f2c0fee17cc6b40a671240d9c30c7a975b9e37385b`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260822T114236Z/agent_outputs/roundtrip_judge.json` (`6b1229988eb754a6e0ab250db08bd63c666aacb12276c611efc7142bdf43633e`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260822T114236Z/agent_outputs/source_contract.json` (`ff2808a497ab6c49ce615fb1ccbc7d04077af06f23cc871a2ffc7f143edf5683`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260822T114236Z/decision.json` (`fa38a6c1c9446061215f4c57cab1a3f80736373d2e548421793c0af1c191e9ef`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260822T114236Z/inputs/blind_dependency_inventory.json` (`683aff668f55ec33424a8df15d3e553199efe250238fcfaf9518adc9da71590d`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260822T114236Z/inputs/blind_dossier.md` (`e1a60ffd699f7af48f91c292abf8b82e63baa02449dfd49387ae4cb197010404`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260822T114236Z/inputs/blind_review_packet.md` (`e1a60ffd699f7af48f91c292abf8b82e63baa02449dfd49387ae4cb197010404`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260822T114236Z/inputs/declaration_dossier.md` (`4c2e3cf0c3b3adb51bc3bd439b43b1b67d5974b444dc40f473a3853a5b261b20`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260822T114236Z/inputs/dependency_inventory.json` (`036ba11f4faa65d5532d4e22cbe1a3df551d1803057fd847f60f176d4970787a`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260822T114236Z/inputs/direct_review_packet.md` (`e199547e94480887a36cfd7e4bc04ecf4e7970df75a1163622521299904017db`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260822T114236Z/inputs/source_locator.json` (`2546b897434d76fcc20e9d3abfa341bcb971f7d2a631227a21cb12673a47c4e3`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/blind_dependency_inventory.json` (`74cb23de4fa14a50453dade253b1bdb034c73139505fff5ae1c928a4622e2df5`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/blind_dossier.md` (`e6325ed646fb36b6a253bbf24b7dd98cddd9305697a7661f0ad37b5286b5eaf7`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/blind_review_packet.md` (`e6325ed646fb36b6a253bbf24b7dd98cddd9305697a7661f0ad37b5286b5eaf7`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/declaration_dossier.md` (`89e224fcae028ae6f11badbad4a996156b24dbcd78b8e43fe47eb1417b333bea`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/dependency_inventory.json` (`028a642e9cd81fcdc279e80cd7b6124885df47a7c09815e676e07538fe44952c`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/direct_review_packet.md` (`a61ce4a9458fd60ea2199d4c305c5d376344a52b36af594b7a7a44584b7239d2`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/source_locator.json` (`c398cc06c724316510b1a49b9f84ca80558b9274361807fd0805accdf45fc2f1`)
