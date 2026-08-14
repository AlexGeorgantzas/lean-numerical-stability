# Faithfulness audit: P03-T3

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `53a5b8e85fc29f632f011ab6f1e06e35c15ebd74211a3015f754ae959f831fa6`
- Paper SHA-256: `952c6827db21fb2a9362b5aa4d38a1b2c75361f2cc7a3badbb7cd4a232d7b7bc`

## Decision

The declaration preserves the exact componentwise true-residual recurrence, solver defect model, residual and update models, infinity-norm condition, condition-number multiplication order, sparsity-dependent gamma factor, constants, higher-order factors, and next-iterate dependence of Theorem 5.1. The disputed imported norm is Mathlib's l-infinity operator norm, and the paper's printed Z_1/M_1 are per-iteration auxiliaries because they explicitly contain G_i. Gamma validity and M1 properties are inherited or derived source facts, not extra restrictions. The only consequential difference is that Lean replaces concrete floating-point execution provenance with an inhabited axiomatic real-trace model. Hence Lean covers every paper case and additional cases, Lean implies the paper theorem, the paper theorem does not imply the full Lean proposition, and faithful-stronger is the consistent accepted classification.

## Implications

- **Lean implies paper:** `yes`. Every paper execution satisfying Theorem 5.1 yields the D010 fields: nonsingularity supplies Ainv, the standard model supplies equations (3.3) and (3.6) and GammaValid, solver condition (2.5) supplies the correction bound, and condition (5.6) supplies the required M1 resolvent properties. Unfolding D002-D006 then gives the paper's exact recurrence.
- **Paper implies lean:** `no`. The paper theorem asserts the recurrence for computed executions of unscaled Algorithm 1.1. Lean asserts it for every abstract real trace satisfying the local analytic certificate, including inhabited traces with no finite-format storage or valid step-1 solve. The paper statement therefore does not cover the full Lean domain.

## Findings

- **note / model-domain-generalization:** The declaration proves the same recurrence on a strictly larger, inhabited domain, which is genuine nonvacuous strength.
- **note / explicit-inherited-facts:** These fields do not reduce applicability relative to valid paper cases and therefore do not reverse either implication.
- **note / auxiliary-indexing:** Lean's explicit iteration arguments resolve the operational dependence consistently without altering W_i, y_i, or the theorem's scope.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `unclear` |
| `S04` | `pass` | `unclear` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `unclear` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `unclear` |
| `S10` | `pass` | `unclear` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `unclear` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `89` dependencies (`0` hash-reused meanings); unclear: `D024, D080`.
- Direct judge covered `89` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

- The PDF does not explain why the auxiliaries are printed with subscript 1 rather than i. The editorial intent remains unknown, but their displayed dependence on G_i within a derivation for arbitrary i determines the task-specific semantics and does not affect the classification.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/agent_outputs/adjudicator.json` (`c8a4593602c99bfc396cb5d7c1840cf3adb92928466bcfe51964e9b95c6f3270`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/agent_outputs/blind_translation.json` (`c57d8a2af85c56519232d3152ae6bf5ae10b6600ac2fdcefe2dcee103b1ed481`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/agent_outputs/direct_judge.json` (`a6759ea30a04febea600b2701b130e16f1495540d74300dafffb61a83c387f97`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`e4206e667175a858e0c1cc0ea11ee69f378055ed2f0fe24845158f43c8d9b84e`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/agent_outputs/source_contract.json` (`03811f34f179e816698a0e2a6c6dbaa4bb0f205cb061230ea626d1a391e7e762`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/decision.json` (`6ef06227fdfd338be415fe130f25a928eff10d31ffac504f9f28826f80805b7f`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/history/20260814T141347Z/agent_outputs/blind_translation.json` (`08b50e6c847c83f0fce1bffba6f46baecb673551e64c5a963a8d5bec7998d440`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/history/20260814T141347Z/agent_outputs/direct_judge.json` (`7d3f07890543e5c9fda7109a1bc4223d41877e03efcdab3916f9e2374007050e`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/history/20260814T141347Z/agent_outputs/paper_source_contract.json` (`cc0f2d27697c7df47ddee702a54285359037d701ffa45ec71a92ca67f9cf3902`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/history/20260814T141347Z/agent_outputs/roundtrip_judge.json` (`48126638f9aa05fab979a13e162306bcdcaf7647da0e552539fbb7dafb0cdced`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/history/20260814T141347Z/agent_outputs/source_contract.json` (`7933032dc0a3d5f1fc45dfb3e4929f648721d76081fe39d63e17ce18d1c91fd5`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/history/20260814T141347Z/decision.json` (`d58585bc427ad3a439afe08e53998387d065d2e9a0e5a323341be1a5763adb1e`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/history/20260814T141347Z/inputs/blind_dependency_inventory.json` (`1175e5bede39281fdd034b44dd127f9344547de3eec9363450133aaf500a9f4f`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/history/20260814T141347Z/inputs/blind_dossier.md` (`f65c7799cf5deaba0f4b3a4f91c5c26548a6447e18d4e7a8956425ee7b5b5375`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/history/20260814T141347Z/inputs/blind_review_packet.md` (`f65c7799cf5deaba0f4b3a4f91c5c26548a6447e18d4e7a8956425ee7b5b5375`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/history/20260814T141347Z/inputs/declaration_dossier.md` (`e0a6e87d157d45146c6d4e4f0081ea2901cf732091e7b1ae07f12efca1ee7b66`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/history/20260814T141347Z/inputs/dependency_inventory.json` (`9cdc9beb61e6936708b2647c847d09bae843bd339bd9420ce881c38f471ec933`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/history/20260814T141347Z/inputs/dependency_reuse_direct.json` (`db6af2afac4a6b35b33d3997f89d8282465ba57db5baa1cad99cabf406d5740f`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/history/20260814T141347Z/inputs/direct_review_packet.md` (`db9f8a5f225bf9a670778a9b2d9d796c127d3521ba99660aaf35baaadfa778e8`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/history/20260814T141347Z/inputs/paper_source_locator.json` (`d325b31e2cf1ecac253237196c87cfb8e169960305af1f36083a03802a8829df`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/history/20260814T141347Z/inputs/source_locator.json` (`b31e761652558dc922a68a035298fc1b28b7dde246480a15f6c278f9b531100b`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/inputs/blind_dependency_inventory.json` (`720263ee397c15bfbbe7ae23ae4ab8c75c86f29ceba4e471d59b36b1dd25b774`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/inputs/blind_dossier.md` (`aa86add61a2026e2ffb5a0bee6381356952ae080de888b2763dd9b42cb23a301`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/inputs/blind_review_packet.md` (`aa86add61a2026e2ffb5a0bee6381356952ae080de888b2763dd9b42cb23a301`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/inputs/declaration_dossier.md` (`7d20717abc21f33d7b70fd6e26dc5f4bf4a96c7a6718c8117ef4fe978af3affa`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/inputs/dependency_inventory.json` (`fab004f8c32edad266170c8e267996690e40c54623834da8e17f2461bbb54a0f`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/inputs/direct_review_packet.md` (`36cb0f1d4f35b61c8caac2ee898c3c5c098e872da65ec5aecedcfa19ab76052a`)
- `paper_bencmark/highambench/tasks/P03/T3/faithfulness/inputs/source_locator.json` (`d566e054743dd83d8a6aa094abdd2308538e965a6f62c9830b313de8fedae5bc`)
