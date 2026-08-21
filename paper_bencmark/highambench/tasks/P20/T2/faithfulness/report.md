# Faithfulness audit: P20-T2

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `2a604cf4f4cd6b18f577e1a745ab2cd8d552d71ed6079b5b7b99bd36b6a37acc`
- Paper SHA-256: `ad830de20a73ff77b6e457921892b3250ba9ff70f487501979ee3f1c5f3f31e2`

## Decision

The verified PDF has the supplied SHA-256. The declaration exactly represents the two complete post-(3.26) underflow terms, their constants, inverse powers, shared dimension, inequality direction, and maximum-row-sum matrix infinity norms. Its hypotheses also suffice to derive the paper's scalar comparison without cancelling the common factor, so scalar-versus-complete scope is not a defect. D004 and D038 are numeral-elaboration infrastructure only. The decisive mismatch is hGg. Literal Model 1 defines the two subnormal regimes independently, and the input-gradual/accumulator-no-subnormal pairing can violate Gmin <= gmin and the claimed comparison even with theta >= 1. Moreover, Gmin <= gmin is stronger than the actual condition Gmin <= theta*gmin. It is therefore an extra restriction, not an implicit necessary premise or genuine strengthening. The paper's asserted result specializes to Lean, but Lean does not cover the paper's full literal domain, yielding not-faithful-weaker.

## Implications

- **Lean implies paper:** `no`. Literal Model 1 admits a gradual-underflow input format paired with an accumulation format lacking subnormals. In that branch, U <= u and Fmin <= fmin do not imply Gmin <= gmin or even Gmin <= theta*gmin. The explicit nondegenerate t = T = 3 example satisfies theta >= 1 but fails the paper comparison and does not satisfy hGg, so the Lean theorem cannot recover every source-stated case.
- **Paper implies lean:** `yes`. After aligning the paper quantities with the declaration and restricting to the declaration's added hypotheses, the paper explicitly asserts the scalar comparison and the resulting complete contribution ordering. Multiplication by 4 n^2 N(A)N(B) is valid because this factor is nonnegative, including when it is zero. Thus the paper's asserted broader-domain result specializes to the Lean statement.

## Findings

- **major / extra underflow-envelope restriction:** The declaration excludes nondegenerate cases in the paper's literal Model 1 domain and therefore formalizes a weaker, repaired statement rather than the stated comparison.
- **note / premise strength:** hGg is sufficient but not necessary when theta > 1, so it cannot be justified as merely exposing the exact necessary premise.
- **note / scalar and complete-term scope:** The absence of a syntactic scalar conclusion and the inability to cancel a zero common factor do not create an additional faithfulness failure.
- **note / matrix infinity norm:** The norm factors faithfully match the paper.
- **note / degenerate dimensions:** These added cases collapse through a zero dimension or norm factor and are degenerate extensions, not genuine theorem strength.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `pass` | `fail` |
| `S04` | `unclear` | `fail` |
| `S05` | `pass` | `fail` |
| `S06` | `pass` | `fail` |
| `S07` | `pass` | `not-applicable` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `unclear` |
| `S10` | `pass` | `pass` |
| `S11` | `unclear` | `fail` |
| `S12` | `pass` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `unclear` | `unclear` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `52` dependencies (`0` hash-reused meanings); unclear: `D004, D038`.
- Direct judge covered `52` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

- The PDF does not state whether the authors intended to exclude the input-gradual/accumulator-no-subnormal pairing or intended an additional envelope-order premise. This unresolved authorial intent does not change the classification against literal Model 1.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/agent_outputs/adjudicator.json` (`ad41868e930305a968fb864a7bc8e269f16d0f3d57a5df04d408e2a3e517d035`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/agent_outputs/blind_translation.json` (`08d68e8e62f82b8e4dfba0098caec6fb5d801c13099556e3c2ba5a71eaa3413b`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/agent_outputs/direct_judge.json` (`ef4023e603a5bb3e6b30a789a7078ffd018aebf2fbecb90bdb9acb809b194c2c`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`2c38d4b593d56e19106760aef5f78919274df0f5b7a698fb7d4adf49edffc539`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/agent_outputs/source_contract.json` (`0811d8294b0f4bebd6348a1ecf0027000bca86a7d4401c71e8d0b53d46bcedcc`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/decision.json` (`c57ad736ffb6bffbf73504fc6335b6ff745d6cf918d1be061dd5efd60ad4c0b4`)
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
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/blind_dependency_inventory.json` (`1a83006084c6376cdf6437c5651212de26811997d787db05ba649a731e05309d`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/blind_dossier.md` (`c2388cd724de72255447efe8b79e9bbf7766b40b34b9df48f9edfcd003fff5ee`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/blind_review_packet.md` (`c2388cd724de72255447efe8b79e9bbf7766b40b34b9df48f9edfcd003fff5ee`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/declaration_dossier.md` (`9562489ddc39ccdd86e00507acffae6dce62fa0e8550d3e362c04aab5d95a763`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/dependency_inventory.json` (`98f119726a8bbffa424a3f5bcfce7f6afc8066774fc87eb446d7cc817eb5fbfc`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/direct_review_packet.md` (`0177cd6507f500b555c446a84dc299cbabb01caf40bc4d6920b03d30483c6176`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/source_locator.json` (`711e033c0b68bfa2c7f192711a38b1f6e378d8e07d0a6164a29bf6cb9483ca6b`)
