# Faithfulness audit: P19-T2

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `f8110a6e567310af2cbdf98ff75fc52acbb6806106a7b1553358b6e1a5bf32e7`
- Paper SHA-256: `67af427c72ae891b7863e386db542ef775b1e3eb306f812bb1a78bdbef86aaad`

## Decision

Primary PDF evidence resolves S09 in favor of the direct judge's pass: choosing kappa_F is a declared specialization permitted by the paper, although the source intentionally leaves unqualified kappa nonunique. That resolution does not repair the proposition's logical changes. The suitable dimension and its spectral evidence are supplied as run data, the Appendix-A forward analysis is required for every M_R before invoking the theorem, and the fixed first-order statement is replaced by a filter-asymptotic proposition with an exact Big-O remainder. The assumptions are satisfiable, but the apparently stronger remainder statement holds only under substantially reduced applicability and conclusion-bearing hypotheses. Consequently neither implication holds, so the correct classification is not-faithful-different and the task is not accepted.

## Implications

- **Lean implies paper:** `no`. The Lean result applies only after a suitable dimension, sufficient spectral evidence, a filter-indexed vanishing-precision regime, and forward-analysis certificates for every right-preconditioner pair have been supplied. It therefore does not establish the paper's theorem for every instance satisfying only the paper's original static Algorithm 2 hypotheses.
- **Paper implies lean:** `no`. The paper derives a result for fixed parameters and suppresses unquantified second-order terms. It does not provide a filter-indexed family tending to zero, a preselected dimension valid eventually, an exact Big-O remainder, exact polynomial coefficients, or the universally quantified propagation certificates required to construct the Lean execution.

## Findings

- **critical / existential-witness-preloaded:** The paper's principal existential achievement is moved into the theorem input.
- **critical / derived-forward-analysis-assumed:** The target recombines conclusion-bearing certificates instead of deriving Theorem 3.1 from conditions (3.2)-(3.6).
- **major / asymptotic-model-substitution:** This simultaneously narrows applicability and asserts unsupported asymptotic structure, so it is not genuine theorem strengthening.
- **minor / polynomial-factor-contract:** The declaration invents exact source data while omitting the paper's low-degree restriction.
- **note / condition-number-resolution:** The declaration's explicit kappa_F interpretation is admissible and is not an independent faithfulness defect.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `pass` |
| `S06` | `fail` | `fail` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `unclear` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `155` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `155` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D004, D005, D012, D013, D016, D019, D020, D024, D025, D030, D031, D032, D033, D034, D035, D036, D037, D039, D041, D049, D059, D060, D061, D066, D071, D076, D082, D083, D084, D129, D143`.

## Remaining uncertainties

- The PDF intentionally does not assign a unique condition-number variant to every unqualified kappa occurrence. The adjudication establishes that the declaration's explicit kappa_F choice is admissible, not that it is uniquely intended; this uncertainty does not affect the final classification.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/agent_outputs/adjudicator.json` (`1d86967092d788701e0e2ee23ccd2a180b15cba48376148b855fb8e46d8a6438`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/agent_outputs/blind_translation.json` (`1fce5e1534fd1862d1d68f63bd2cd9b0b17e4a8639c8d390742780c5cec1ccbd`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/agent_outputs/direct_judge.json` (`580c6e0b96424ffcb3a6a0baf15cdf4f5cccd27f3149db7e599ff30e934224b9`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`95caf563fcbcdffadf35a2b40760a1c3182c9e8d517c17f7a8cffc789d55e615`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/agent_outputs/source_contract.json` (`286e19871dc52069751cba3abd7b3f9fab6aa1d32aad6223187ec4650d8781aa`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/decision.json` (`90d46a8e78141e933fd3434ca5623767fd0d980da78fd3e36b85cc675318b820`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260821T034444Z/agent_outputs/blind_translation.json` (`5ece5e5732c21b0e179d6bee4aecf8bf5db288c1b68d0d545f76137b156636c0`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260821T034444Z/agent_outputs/direct_judge.json` (`a41deaf570d409888e2b2e08bc2577e57bf8c99388e7c9ed912a8c3c5abc869f`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260821T034444Z/agent_outputs/paper_source_contract.json` (`282bdf4dba3e70c740465a2c4663b96debd1a66ef82c3debf273ad41cdbf76e0`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260821T034444Z/agent_outputs/roundtrip_judge.json` (`24afa3b2a0a0cb5ffc638262914d28638a8d19c35ed983ae669eac2a99b677f1`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260821T034444Z/agent_outputs/source_contract.json` (`dd0d2bca250671eb54008fe6991d62753daf66112a7a2271b59c6dcc1567e999`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260821T034444Z/decision.json` (`f4bacc33043fba7f132cd6b9e4227176eef7bcec965a75ad277dc92b96479de2`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260821T034444Z/inputs/blind_dependency_inventory.json` (`ec138d7e7422dcbc4046b9de8e07396d88b56e6e8add192676de7a2721aad2f3`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260821T034444Z/inputs/blind_dossier.md` (`30488ba9c655efb7e89d355d763b5b315834ffe2b5f091689b780e722e67a310`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260821T034444Z/inputs/blind_review_packet.md` (`30488ba9c655efb7e89d355d763b5b315834ffe2b5f091689b780e722e67a310`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260821T034444Z/inputs/declaration_dossier.md` (`418693f6115bcee06a30e8b43d98426b575cfeaf0efeea1c14dd12781a43e55d`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260821T034444Z/inputs/dependency_inventory.json` (`05e54919f44802e2c919335c432acea16eda5d837976d444a726524a271a4bd1`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260821T034444Z/inputs/dependency_reuse_direct.json` (`12d4bef658bdd1e736e525973b9a4e7bcf7a33e63b0e0cc8f6963605d89757cc`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260821T034444Z/inputs/direct_review_packet.md` (`279dca4b8eac123f63d7a37f7c1fe51271fa672a079b0682f6fe28f5974236aa`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260821T034444Z/inputs/paper_source_locator.json` (`b2b71745c3ba0bc98613f67b2d754faf971558a1974b0f22e4456d4b88500ba1`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260821T034444Z/inputs/source_locator.json` (`41c7217c655d70ebb73d0b6037c21d54f22f6119435a2bb382ff077e98e78af7`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/blind_dependency_inventory.json` (`f982626ee3508d9138b22c53fdc7f555ba069cb0c755cedd57fe95f994dc7b33`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/blind_dossier.md` (`8d9eb971c14b4fab410ede5bffcd01af73db206f005a3152e5258263da69e26b`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/blind_review_packet.md` (`8d9eb971c14b4fab410ede5bffcd01af73db206f005a3152e5258263da69e26b`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/declaration_dossier.md` (`92e3a6b531eaf242e3c552e8073f16ae6857e68f7c9c1bb7499534f65fa40be4`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/dependency_inventory.json` (`4a82dffbc55730e415038cfd3080f8f7367902acd622434b3feb1463c5b6ae1a`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/direct_review_packet.md` (`c658e9eba0d9decddadbbbd12bfae052c8dbe8cf49074e67f7106a4bbd3c2211`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/source_locator.json` (`a3919e68aedc0c649dc78dbd09686fa20956374216ce17671ed9c29eb8d34f46`)
