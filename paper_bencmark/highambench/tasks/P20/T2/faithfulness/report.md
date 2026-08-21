# Faithfulness audit: P20-T2

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `false`
- Target SHA-256: `fb95ee7956f7e12ea8d77a263a09660b727555fa2b3d617185a4baba787e08b0`
- Paper SHA-256: `ad830de20a73ff77b6e457921892b3250ba9ff70f487501979ee3f1c5f3f31e2`

## Decision

After unfolding all dependencies, the theorem states exactly the non-asymptotic equation (3.13) bound for the pre-accumulation input-conversion error: the same theta, dyadic scale inequalities, component count, absolute inner product, infinity norms, constants, underflow regimes, and higher-order terms are present. It is nonvacuous and remains directly linked to the scaled MMA inner-product stage. Its only consequential scope difference is that the formal conversion operation need only satisfy the paper's relative/additive error axioms rather than be operationally specified as nearest representable rounding. Consequently Lean covers the paper case and additional abstract conversion maps, while the paper statement does not assert that full generality.

## Implications

- **Lean implies paper:** `yes`. For a paper input format and safe scaled arguments, instantiate inputRound by the paper's conversion and the model fields by its delta/eta decomposition. The unfolded Lean conclusion is exactly equation (3.13) for epsilon_1.
- **Paper implies lean:** `no`. The paper states the result for its actual nearest-representable conversion model. It does not itself quantify over arbitrary format-index families or arbitrary real-to-real conversion maps that merely satisfy the same error equations, whereas the Lean theorem does.

## Findings

- **note / abstract-rounding-generalization:** The target proves the same bound for a broader class of conversion maps. This is genuine stronger scope, not a weakening or a different error result.
- **note / zero-vector-domain:** This resolves the source passage's undefined zero-vector ratios and preserves the intended nonzero scaling construction.
- **major / floating-point-model-generalization:** The numerical bound remains valid and covers the paper as an instance, but the reverse implication fails because the formal statement proves a proper analytic generalization of the paper's concrete floating-point result.
- **minor / binder-index-generalization:** At a selected index the parameters coincide with the paper's parameters, so the formula is unchanged, but the binder structure is not literally equivalent.
- **note / local-domain-specialization:** This restricts the proposition to the domain where the paper's displayed scaling construction is defined and does not invent a zero-vector interpretation.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `pass` | `pass` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `101` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `101` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/agent_outputs/blind_translation.json` (`245a9a9a1cc13625d3148141cf9579950661072459d53875f4768f975da13599`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/agent_outputs/direct_judge.json` (`583d4e63cc0ce8d27d9f57e996f89585afac39db0f5a0b1e363a6a994cca6c26`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`e6e0376e474dbd5caf7c6b7a664e402ff6e367051871291137fcebadba61e9d2`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/agent_outputs/source_contract.json` (`19634ef8e245ba7a9239a2ec7cb6dfbc2bdb2ad9009f71ff7c6b9404b0bc7e33`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/decision.json` (`e082c9caa673dd57bd8e7252f0909acf1ea902fb0e1f23f07b738adb3a58f212`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T045309Z/agent_outputs/adjudicator.json` (`3f778c634d05a2451c8059cac8b7cf5f3d67080c1a87ecfeed971210640cbe18`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T045309Z/agent_outputs/blind_translation.json` (`096f66df2a5c2c8874ccf6722fc12b9ae49a4f9fbb2f05368fbe1358a57d5cf2`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T045309Z/agent_outputs/direct_judge.json` (`acacda49c8ccdd4f138001e07de79a4bfcdfb1c355a69f33eb09753a88c3f5eb`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T045309Z/agent_outputs/paper_source_contract.json` (`a0c8bbaa2e261f7adc023b1698c08de77fd260aafddc9aa341073c2704530e40`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T045309Z/agent_outputs/roundtrip_judge.json` (`6b8a6298e9450e37a021f41941901fe5ce8d4d56ed02020410352e60207e1c6d`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T045309Z/agent_outputs/source_contract.json` (`5baba912e023c835e1bfb52bdc2bf8d16e7db7a0c7aa20318b537211c2414b4d`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T045309Z/decision.json` (`46621fcf09a5edd3d0df5cc74829ada9a5580817ba9045bc3d491f369f4effb2`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T045309Z/inputs/blind_dependency_inventory.json` (`1a83006084c6376cdf6437c5651212de26811997d787db05ba649a731e05309d`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T045309Z/inputs/blind_dossier.md` (`c2388cd724de72255447efe8b79e9bbf7766b40b34b9df48f9edfcd003fff5ee`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T045309Z/inputs/blind_review_packet.md` (`c2388cd724de72255447efe8b79e9bbf7766b40b34b9df48f9edfcd003fff5ee`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T045309Z/inputs/declaration_dossier.md` (`dcb39a6b7008c87d70a78328f1ff0eb906b2bd886467a76b8ddb6acdcdb0afa1`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T045309Z/inputs/dependency_inventory.json` (`98f119726a8bbffa424a3f5bcfce7f6afc8066774fc87eb446d7cc817eb5fbfc`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T045309Z/inputs/dependency_reuse_direct.json` (`3ce0db4772d618791b5a41160581d16516737cd7d08639e74da477e016f726c8`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T045309Z/inputs/direct_review_packet.md` (`2364b9a47ba52f22b5a2a294539ab9870a8a20ff2b927fc142f9336975e54d70`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T045309Z/inputs/paper_source_locator.json` (`413757004ac4d15ac7e55e926e2486e54bdac2db1523d83303ddb4cbffe644f4`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T045309Z/inputs/source_locator.json` (`711e033c0b68bfa2c7f192711a38b1f6e378d8e07d0a6164a29bf6cb9483ca6b`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T095413Z/agent_outputs/adjudicator.json` (`ad41868e930305a968fb864a7bc8e269f16d0f3d57a5df04d408e2a3e517d035`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T095413Z/agent_outputs/blind_translation.json` (`08d68e8e62f82b8e4dfba0098caec6fb5d801c13099556e3c2ba5a71eaa3413b`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T095413Z/agent_outputs/direct_judge.json` (`ef4023e603a5bb3e6b30a789a7078ffd018aebf2fbecb90bdb9acb809b194c2c`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T095413Z/agent_outputs/roundtrip_judge.json` (`2c38d4b593d56e19106760aef5f78919274df0f5b7a698fb7d4adf49edffc539`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T095413Z/agent_outputs/source_contract.json` (`0811d8294b0f4bebd6348a1ecf0027000bca86a7d4401c71e8d0b53d46bcedcc`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T095413Z/decision.json` (`c57ad736ffb6bffbf73504fc6335b6ff745d6cf918d1be061dd5efd60ad4c0b4`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T095413Z/inputs/blind_dependency_inventory.json` (`1a83006084c6376cdf6437c5651212de26811997d787db05ba649a731e05309d`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T095413Z/inputs/blind_dossier.md` (`c2388cd724de72255447efe8b79e9bbf7766b40b34b9df48f9edfcd003fff5ee`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T095413Z/inputs/blind_review_packet.md` (`c2388cd724de72255447efe8b79e9bbf7766b40b34b9df48f9edfcd003fff5ee`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T095413Z/inputs/declaration_dossier.md` (`9562489ddc39ccdd86e00507acffae6dce62fa0e8550d3e362c04aab5d95a763`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T095413Z/inputs/dependency_inventory.json` (`98f119726a8bbffa424a3f5bcfce7f6afc8066774fc87eb446d7cc817eb5fbfc`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T095413Z/inputs/direct_review_packet.md` (`0177cd6507f500b555c446a84dc299cbabb01caf40bc4d6920b03d30483c6176`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/history/20260821T095413Z/inputs/source_locator.json` (`711e033c0b68bfa2c7f192711a38b1f6e378d8e07d0a6164a29bf6cb9483ca6b`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/blind_dependency_inventory.json` (`983e77423a244cab54d225d73aa095e64cf9b6df41189f869444f0db8a24cea1`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/blind_dossier.md` (`8235e77cd8272793622baf6e14501b7b74fa8844435fbfdd578d80382e0fb397`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/blind_review_packet.md` (`8235e77cd8272793622baf6e14501b7b74fa8844435fbfdd578d80382e0fb397`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/declaration_dossier.md` (`637dbaa6f71d4276c0bbd7ff56bc2ee8b7ef6b372f80f9624fc9d2ae52f38572`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/dependency_inventory.json` (`9e54b840a3b8001d07d089bbd34d142fda355270b76ed2ebc6c7954472e23070`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/direct_review_packet.md` (`cc6142ef4c8825767cd0bb18a6bccff255a6b126da16172295492d0965115c94`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/source_locator.json` (`b05fecfed8d3a4d71c8aa470676ebd3afc0e4feab7eec1c7c35beb9818fe4c09`)
