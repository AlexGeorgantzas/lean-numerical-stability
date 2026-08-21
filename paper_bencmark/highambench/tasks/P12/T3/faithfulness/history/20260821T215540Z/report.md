# Faithfulness audit: P12-T3

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `358fc92a23f1728d172df527442e4df0dd28a617b644d63cf626cd2a188b4d6c`
- Paper SHA-256: `0569d969cebaabe42de69fef10fa91002af12d62149af7485d0712414b53c2a1`

## Decision

The trace fields, algorithm order, exact-versus-computed distinction, rounding predicates, and final exact identity faithfully reflect the paper. The decisive defect is the antecedent: run assumes several proof-supporting envelope, grid, and candidate facts that the paper neither states nor equates with absence of underflow and overflow. Those assumptions exclude concrete valid paper executions. Consequently the paper result specializes to and supports the Lean target, including its stronger unceiled merge bound, but the Lean proposition cannot recover the full paper theorem. It is therefore not-faithful-weaker rather than faithful-stronger.

## Implications

- **Lean implies paper:** `no`. The Lean proposition proves the result only for inhabitants of P12ThreeProductExecution. Valid paper executions need not produce such an inhabitant. For beta=2, p=3, emin=0, emax=2, the exact product of 1 and 7 is 7 with no underflow or overflow, but P12TwoProductExecution.mk requires the envelope 8*1*7=56 and its negative to be representable even though the largest magnitude in F is 28. Thus the Lean theorem cannot recover the paper's universal domain.
- **Paper implies lean:** `yes`. Restricting the paper's argument to traces admitted by run yields every target conjunct: Theorem 2 proves the two subtraction equalities and exact merge, printed page 397 proves the final addition exact, and equation (18) gives the final product identity. The target's unceiled bound follows from the paper's earlier |s3'| <= (1/2)beta^p beta^e estimate and beta^p >= beta.

## Findings

- **major / hypothesis-domain-narrowing:** The formal theorem excludes legitimate non-overflowing, non-underflowing ThreeProduct executions and therefore does not establish the full benchmark result.
- **minor / ceiling-constant:** For odd radices the written bounds differ. The Lean bound is stronger but derivable from the proof's preceding half-beta^p bound, so this does not cause the failed implication; it is nevertheless not a literal preservation of the displayed condition.
- **major / workflow-hypothesis-strengthening:** Valid source executions can lack a run witness, so the translated theorem proves the result on a strictly narrower domain.
- **major / underflow-model:** The source range hypothesis is replaced by a stronger behavioral certificate rather than preserved as stated.
- **major / ceiling-coefficient:** For odd bases the translated bound is strictly stronger and does not literally reconstruct condition (7), although the paper's preceding B/2 estimate entails it on admitted runs.
- **minor / rounding-mode:** The abstract execution model is broader than the stated Section 4 rounding model, even though Theorem 2's faithful-subtraction result supports the same exact merge.

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
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `pass` |
| `S16` | `pass` | `fail` |

## Dependency coverage

- Blind translator covered `101` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `101` dependencies (`0` hash-reused interpretations); failing or unclear: `D007, D021, D032, D042`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/agent_outputs/blind_translation.json` (`fbe70027ac3ecff5289e85d3927269092dfa4bab32409c98002f3e4ec97a7683`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/agent_outputs/direct_judge.json` (`f83e3cec979c5a5c0699e839cd8bb0274ae18044b87f2df53b8005956c4cbf68`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`cf76f35ea9652b67567d34568d87631180a6c5bf7e530864acb2c7472b5eabd4`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/agent_outputs/source_contract.json` (`dba1a57cf02fa3eaceb330b4ed432b8442945f7c367dace90813741344efae9b`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/decision.json` (`4478971c771fd272f8d8e7021577a98807cd7b2af5589f86a51615f07d8d9772`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260815T085448Z/agent_outputs/adjudicator.json` (`135f4865341fa211c809a54756f870ff06d99b74dc587e967faf9876b3989804`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260815T085448Z/agent_outputs/blind_translation.json` (`2ecde84e09694ba489f208e1a1430e9e3056cc8ed4d4054ec1d9902e03e700bd`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260815T085448Z/agent_outputs/direct_judge.json` (`ab73ab9377dd9a43fb48e1a1c82c73deb79d2dbc12a3d6f180d8ff2dc645bce3`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260815T085448Z/agent_outputs/paper_source_contract.json` (`c14eaa2ba1c25d2284fb972ef8a21fb4aa3b9f4953061dea7bb0ea5b382a6321`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260815T085448Z/agent_outputs/roundtrip_judge.json` (`07eb011473a8d78b8f3c9b2ab892527da67a72c054979b5a5e32347a6d96c963`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260815T085448Z/agent_outputs/source_contract.json` (`f1c66425b94e5dee3988a2d95781b74c88f9156e8b34310eb820a007b13fb55b`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260815T085448Z/decision.json` (`675b0224c18b656f1453ecb1c8771bd802adc7e239e3ba16763fa18d6727a773`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260815T085448Z/inputs/blind_dependency_inventory.json` (`9f884d74066175525bc597b4b759b53ccaa94284b5df406baf5b6e926abfbad1`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260815T085448Z/inputs/blind_dossier.md` (`387a94a0ed630a014aeb62bd16ed23692e5e54b5da5320b8d1129cd826e7d26f`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260815T085448Z/inputs/blind_review_packet.md` (`387a94a0ed630a014aeb62bd16ed23692e5e54b5da5320b8d1129cd826e7d26f`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260815T085448Z/inputs/declaration_dossier.md` (`5cdceed5c2dc410f1e9b8aef7fcece10df0dbc87e32b329a9f170f2a06e3eb8e`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260815T085448Z/inputs/dependency_inventory.json` (`5318e32a090163d310aef2bef53d3d8a3bb043e47155d6519cc2de8a7f4d07aa`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260815T085448Z/inputs/dependency_reuse_direct.json` (`95177992492e4cddf601e303ff769362ad201a58412c0a62ca2dddc1a89a8de8`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260815T085448Z/inputs/direct_review_packet.md` (`7f26b97f92c512624d81e9a10c3b12748f39e54d588cfdf2db06d578d38e231a`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260815T085448Z/inputs/paper_source_locator.json` (`515de0f8e7e7ece14b209a55702074a38799c848bbb9eb747b29a9993464642f`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260815T085448Z/inputs/source_locator.json` (`10ee0dcce1c7d32b3d30bf5a002cd2a57ec68d70bb00b2ea54635a716894ca68`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/inputs/blind_dependency_inventory.json` (`a0e01e72b4adb63074f1cbdf3a78dac40bfa582490299c6e7049a4ac575a9546`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/inputs/blind_dossier.md` (`79ad10e20099d2bc5921421c19013b7ddb46e95c7919a1b4edb2071ce914781c`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/inputs/blind_review_packet.md` (`79ad10e20099d2bc5921421c19013b7ddb46e95c7919a1b4edb2071ce914781c`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/inputs/declaration_dossier.md` (`2e8914b764fda66bad48e4d7b9b4ac7f00f3664854ca21257bc5e8b20747610c`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/inputs/dependency_inventory.json` (`1ccdb18058de97fa54e1056379776a0e30b59a955f5d33d99f9f8cef72f6c6b0`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/inputs/direct_review_packet.md` (`d01ca8d8ef1c3bf6d93187ae236790d86a965b77994cd2c708e633e54edfb30f`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/inputs/source_locator.json` (`44a4d98e6b760df6e18d1c35a2146ea2e906338fd78728e7dc3747eae0df0c4c`)
