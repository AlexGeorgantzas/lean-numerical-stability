# Faithfulness audit: P12-T3

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `d2835574e18a08cca5b90a4ccd815014a63dcad249e9cf2917988ac99957ab4d`
- Paper SHA-256: `0569d969cebaabe42de69fef10fa91002af12d62149af7485d0712414b53c2a1`

## Decision

The format, representation semantics, ceiling scope, nearest rounding, operation order, noOverflow coverage, condition-(7) witness, and all stated intermediate conclusions otherwise match the cited paper. Least-representation witnesses are harmless because every representable value has a minimum feasible exponent in the finite exponent interval. The decisive defect is the second TwoProduct call's raw input-grid argument to D049: it imposes a half-beta^p grid bound where the paper permits a half-beta^{2p} bound. A nontrivial formal run demonstrates nonvacuity, while the explicit 7*7*7 execution demonstrates genuine loss of paper-valid behavior. Thus the proposition is a nonfaithful weaker specialization, not a stronger theorem.

## Implications

- **Lean implies paper:** `no`. The Lean theorem proves the paper conclusion only for traces admitting its stronger run witness. For beta=2,p=3,emin=0,emax=10 and x1=x2=x3=7, a valid paper execution is th=48, tl=1, s1=320, a2=16, a3=7, a4=0, s2=24, t=8, r=-1, s3=-1. Equation (17) permits a2 because ulp(336)=64 and 16<=32, but the formal second split demands 16<=0.5*8=4. Hence this valid paper execution has no run witness.
- **Paper implies lean:** `yes`. Assuming the narrower formal run premise, equation (17), nearest rounding, the range assumptions, Theorem 2, and the proof of Lemma 4 establish the condition-(7) witness, both exact FastTwoSum subtractions, the merge identity, exact final addition, and equation (18). The erroneous low-grid clause is an extra premise, so it does not obstruct this implication direction.

## Findings

- **major / second-product-grid-overconstraint:** The run relation excludes valid nontrivial ThreeProduct executions. The theorem therefore covers a strict subset of the paper's domain and cannot faithfully represent Lemma 4.
- **major / added product-grid domain restriction:** A valid nonzero ThreeProduct execution in the paper's arbitrary-radix, nearest-rounding, no-underflow/no-overflow model has no translation run. The formal theorem therefore covers a proper subset of Lemma 4's domain.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `fail` | `pass` |
| `S04` | `fail` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `fail` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `fail` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `pass` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `107` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `107` dependencies (`0` hash-reused interpretations); failing or unclear: `D006, D021, D033, D042, D049`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/agent_outputs/blind_translation.json` (`3c68ec45281674ad12b95d7c5655459d1cb143efe16c82e6b7d9f78eb582b669`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/agent_outputs/direct_judge.json` (`9897b2c9fb86e32f1be059d12ef28cb4a79fa31e8927cf9d453bad69eb5f1dbd`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`0019f90be044c933cc5755f07ff8fb42683850cffc088cbd29449cc0de7e58ad`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/agent_outputs/source_contract.json` (`1b354a5cd2f347a947731b3dd6acebab802c9bd74e797ec1b49a9bfb9e19947f`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/decision.json` (`fb6a90ee1009f32cd01ee60e8d554424fb730b51089901fe3f701a009e79bcc9`)
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
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260821T215540Z/agent_outputs/blind_translation.json` (`fbe70027ac3ecff5289e85d3927269092dfa4bab32409c98002f3e4ec97a7683`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260821T215540Z/agent_outputs/direct_judge.json` (`f83e3cec979c5a5c0699e839cd8bb0274ae18044b87f2df53b8005956c4cbf68`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260821T215540Z/agent_outputs/roundtrip_judge.json` (`cf76f35ea9652b67567d34568d87631180a6c5bf7e530864acb2c7472b5eabd4`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260821T215540Z/agent_outputs/source_contract.json` (`dba1a57cf02fa3eaceb330b4ed432b8442945f7c367dace90813741344efae9b`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260821T215540Z/decision.json` (`4478971c771fd272f8d8e7021577a98807cd7b2af5589f86a51615f07d8d9772`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260821T215540Z/inputs/blind_dependency_inventory.json` (`a0e01e72b4adb63074f1cbdf3a78dac40bfa582490299c6e7049a4ac575a9546`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260821T215540Z/inputs/blind_dossier.md` (`79ad10e20099d2bc5921421c19013b7ddb46e95c7919a1b4edb2071ce914781c`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260821T215540Z/inputs/blind_review_packet.md` (`79ad10e20099d2bc5921421c19013b7ddb46e95c7919a1b4edb2071ce914781c`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260821T215540Z/inputs/declaration_dossier.md` (`2e8914b764fda66bad48e4d7b9b4ac7f00f3664854ca21257bc5e8b20747610c`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260821T215540Z/inputs/dependency_inventory.json` (`1ccdb18058de97fa54e1056379776a0e30b59a955f5d33d99f9f8cef72f6c6b0`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260821T215540Z/inputs/direct_review_packet.md` (`d01ca8d8ef1c3bf6d93187ae236790d86a965b77994cd2c708e633e54edfb30f`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/history/20260821T215540Z/inputs/source_locator.json` (`44a4d98e6b760df6e18d1c35a2146ea2e906338fd78728e7dc3747eae0df0c4c`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/inputs/blind_dependency_inventory.json` (`c6b1adaa533d8390cb8dde32d22b823c7c3a281f2ef1186a3c0aa4e846aee5f9`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/inputs/blind_dossier.md` (`15e877f9d91c388022cb3181f465051ac87e6479ef7c8d6a140f2e0f8513dab7`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/inputs/blind_review_packet.md` (`15e877f9d91c388022cb3181f465051ac87e6479ef7c8d6a140f2e0f8513dab7`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/inputs/declaration_dossier.md` (`482afb5e32edd1f8c05a2f52099adc2a20ef9f6beb9565b98cfe66b36eccb21f`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/inputs/dependency_inventory.json` (`52c927634b7b7c6e9660b9825aa7f4d8b9fb25df6209948dd4f85892efd9785a`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/inputs/direct_review_packet.md` (`30ab023ccc6e97a29bbc5697e1b679521bcf0aa6a8eb35077427084951dd4f09`)
- `paper_bencmark/highambench/tasks/P12/T3/faithfulness/inputs/source_locator.json` (`44a4d98e6b760df6e18d1c35a2146ea2e906338fd78728e7dc3747eae0df0c4c`)
