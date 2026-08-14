# Faithfulness audit: P20-T2

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `2a604cf4f4cd6b18f577e1a745ab2cd8d552d71ed6079b5b7b99bd36b6a37acc`
- Paper SHA-256: `ad830de20a73ff77b6e457921892b3250ba9ff70f487501979ee3f1c5f3f31e2`

## Decision

The source locator selects the exact local comparison following equation (3.26), so the declaration need not reproduce the complete approximate forward-error bound. Its two envelope formulas and matrix infinity norms match that comparison exactly. However, the paper states the ordering for Model 1 when theta >= 1, while Lean requires Gmin <= gmin explicitly. The paper's piecewise underflow definitions do not derive that premise in every mixed subnormal-mode case. Lean therefore formalizes a restricted repair of the claimed comparison rather than the comparison under the paper's written hypotheses, making it not-faithful-weaker.

## Implications

- **Lean implies paper:** `no`. The paper claims the envelope comparison for Model 1 when theta >= 1. Lean cannot recover all such source cases because it additionally requires Gmin <= gmin, and the written Model 1 does not imply that condition for the mixed case of gradual input underflow with accumulation subnormals unavailable.
- **Paper implies lean:** `yes`. Under the source-to-Lean parameter mapping, the paper asserts the same envelope ordering under weaker source conditions. Restricting to cases satisfying Lean's additional Gmin <= gmin premise and multiplying by the common nonnegative factor 4n^2||A||_infinity||B||_infinity yields the Lean conclusion.

## Findings

- **major / hypothesis-substitution:** The declaration proves only the residual monotonicity argument and does not cover every configuration addressed by the written paper claim.
- **major / mixed-subnormal-mode-gap:** The added Lean premise repairs the source derivation by excluding a problematic case, thereby weakening rather than faithfully formalizing the stated result.
- **minor / degenerate-dimensions:** Lean includes trivial zero-coefficient cases outside the intended paper domain.
- **note / local-envelope-match:** Once the additional ordering premise is supplied, the selected local comparison has the correct constants, norms, strictness, and direction.
- **note / nonvacuity:** The theorem is not globally vacuous, but its added premise still reduces source applicability.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `pass` | `fail` |
| `S06` | `pass` | `fail` |
| `S07` | `pass` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `fail` | `fail` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `fail` |
| `S14` | `pass` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `fail` |

## Dependency coverage

- Blind translator covered `52` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `52` dependencies (`16` hash-reused interpretations); failing or unclear: `D007, D028`.

## Remaining uncertainties

- The PDF does not state whether input and accumulation subnormal availability must be coupled. An unstated coupling could exclude the mixed mode that invalidates the paper's stated derivation, but written Model 1 does not impose it.
- The paper gives no convention for zero-dimensional matrices, while Lean permits them and defines an empty maximum as zero; this affects only additional degenerate Lean instances.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/agent_outputs/adjudicator.json` (`3f778c634d05a2451c8059cac8b7cf5f3d67080c1a87ecfeed971210640cbe18`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/agent_outputs/blind_translation.json` (`096f66df2a5c2c8874ccf6722fc12b9ae49a4f9fbb2f05368fbe1358a57d5cf2`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/agent_outputs/direct_judge.json` (`acacda49c8ccdd4f138001e07de79a4bfcdfb1c355a69f33eb09753a88c3f5eb`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/agent_outputs/paper_source_contract.json` (`a0c8bbaa2e261f7adc023b1698c08de77fd260aafddc9aa341073c2704530e40`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`6b8a6298e9450e37a021f41941901fe5ce8d4d56ed02020410352e60207e1c6d`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/agent_outputs/source_contract.json` (`5baba912e023c835e1bfb52bdc2bf8d16e7db7a0c7aa20318b537211c2414b4d`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/decision.json` (`46621fcf09a5edd3d0df5cc74829ada9a5580817ba9045bc3d491f369f4effb2`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/blind_dependency_inventory.json` (`1a83006084c6376cdf6437c5651212de26811997d787db05ba649a731e05309d`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/blind_dossier.md` (`c2388cd724de72255447efe8b79e9bbf7766b40b34b9df48f9edfcd003fff5ee`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/blind_review_packet.md` (`c2388cd724de72255447efe8b79e9bbf7766b40b34b9df48f9edfcd003fff5ee`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/declaration_dossier.md` (`dcb39a6b7008c87d70a78328f1ff0eb906b2bd886467a76b8ddb6acdcdb0afa1`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/dependency_inventory.json` (`98f119726a8bbffa424a3f5bcfce7f6afc8066774fc87eb446d7cc817eb5fbfc`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/dependency_reuse_direct.json` (`3ce0db4772d618791b5a41160581d16516737cd7d08639e74da477e016f726c8`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/direct_review_packet.md` (`2364b9a47ba52f22b5a2a294539ab9870a8a20ff2b927fc142f9336975e54d70`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/paper_source_locator.json` (`413757004ac4d15ac7e55e926e2486e54bdac2db1523d83303ddb4cbffe644f4`)
- `paper_bencmark/highambench/tasks/P20/T2/faithfulness/inputs/source_locator.json` (`711e033c0b68bfa2c7f192711a38b1f6e378d8e07d0a6164a29bf6cb9483ca6b`)
