# Faithfulness audit: P19-T2

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `93526540f05f838dab8c1649079e99d83c23a36134657f262b3bba6909e3290b`
- Paper SHA-256: `67af427c72ae891b7863e386db542ef775b1e3eb306f812bb1a78bdbef86aaad`

## Decision

The authoritative PDF SHA-256 was verified as 67af427c72ae891b7863e386db542ef775b1e3eb306f812bb1a78bdbef86aaad. Primary evidence resolves the disagreement without voting: the PDF states an existential MGS-selected dimension, exact (A.1) coefficients, and an Appendix-A derivation, whereas Lean admits singular Good(k), replaces c(n,k) by unrestricted dimensionFactor, quantifies arbitrary qualitative predicates, and assumes local MGS and Appendix certificates. The round-trip paper_implies_lean=yes verdict depends on enriching the paper with those certificates and therefore is rejected. Because source-invalid Lean models exist while the paper does not entail the exact-only semantics or certificate applicability required by other Lean models, both implications fail and the fixed-vocabulary label is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. Lean admits Good(k) with a singular VHat through 1/0=0, admits singular computed C when small accepts the totalized ratio, permits small=True to erase the paper's numerical-smallness scope, and permits secondOrder=True to trivialize the final estimate. Its arbitrary dimensionFactor and altered (A.1) threshold add further source-invalid models.
- **Paper implies lean:** `no`. The paper contract does not entail applicability or inhabitation of the formal local MGS law and Appendix-A theory for arbitrary semantics. In particular, secondOrder={0} demands exact zero-remainder propagation not supplied by the explicitly first-order paper argument, and the PDF states an existential MGS result with (c(n,k)*u_g+epsilon_c), not the formal local law with dimensionFactor*(u_g+epsilonC). Adding those certificates as extra assumptions is not paper-to-Lean implication.

## Findings

- **critical / zero-reciprocal-conditioning:** Lean can establish the main selected-basis conclusion for a singular computed basis, so Lean does not imply the paper result.
- **critical / unconstrained-first-order-semantics:** The formal theorem ranges from vacuous to trivial to stronger-than-source depending on the semantics argument, defeating either one-way strength classification.
- **critical / conclusion-bearing-assumptions:** The declaration does not independently cover the paper's stated domain, and paper_implies_lean cannot be obtained by supplying these extra certificates.
- **major / A.1-and-dimension-factor:** The epsilon_c coefficient, admissible near-dependence cases, least-squares factor, and final error factor are not uniformly the paper's low-degree c(n,k).
- **major / MGS-selection-contract:** The formal selection premise is neither stated nor entailed by the audited PDF contract.
- **note / faithful-structure-and-norm-specialization:** These are genuine faithful components, but they do not offset the failures in conditioning, assumptions, constants, and first-order semantics.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `pass` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `pass` |
| `S06` | `pass` | `fail` |
| `S07` | `pass` | `pass` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `unclear` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `172` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `172` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D002, D004, D005, D007, D008, D011, D017, D020, D024, D025, D032, D033, D034, D037, D040, D066, D068, D071, D080, D081, D087, D094, D102, D116`.

## Remaining uncertainties

- The PDF intentionally leaves numerical thresholds for its qualitative smallness notation, exact semantics for neglected second-order terms, and the coefficients and degrees of each generic c(n,k) unspecified. This inherent ambiguity does not affect the classification because the zero-reciprocal model, exact (A.1) mismatch, and conclusion-bearing certificate assumptions are explicit.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/agent_outputs/adjudicator.json` (`5b9b3b7189896cc5f5336378508d2b9feb96f4b13f815801441a3630bb5da3e3`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/agent_outputs/blind_translation.json` (`91ea59064870c06f4b7584a4ddd6c0c6f28f57e4dca61b894bbc8152b94ea101`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/agent_outputs/direct_judge.json` (`cc3dcb649df25f62f54b6ef572c26827039bd642588436a339c6b947edf259be`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`98d04d8d3e7d81aa6c55d2269ab6117096782f638306470241dba68e21060aa5`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/agent_outputs/source_contract.json` (`81c8086e3defbfcce94ccb9e11e563eb0835a6a7121ddf5b109280b8b637fce8`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/decision.json` (`b1b34154fbfb21b0718d895308d3bb395a7aca39907162f69137ccc9948cc934`)
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
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260822T004959Z/agent_outputs/adjudicator.json` (`1d86967092d788701e0e2ee23ccd2a180b15cba48376148b855fb8e46d8a6438`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260822T004959Z/agent_outputs/blind_translation.json` (`1fce5e1534fd1862d1d68f63bd2cd9b0b17e4a8639c8d390742780c5cec1ccbd`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260822T004959Z/agent_outputs/direct_judge.json` (`580c6e0b96424ffcb3a6a0baf15cdf4f5cccd27f3149db7e599ff30e934224b9`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260822T004959Z/agent_outputs/roundtrip_judge.json` (`95caf563fcbcdffadf35a2b40760a1c3182c9e8d517c17f7a8cffc789d55e615`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260822T004959Z/agent_outputs/source_contract.json` (`286e19871dc52069751cba3abd7b3f9fab6aa1d32aad6223187ec4650d8781aa`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260822T004959Z/decision.json` (`90d46a8e78141e933fd3434ca5623767fd0d980da78fd3e36b85cc675318b820`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260822T004959Z/inputs/blind_dependency_inventory.json` (`f982626ee3508d9138b22c53fdc7f555ba069cb0c755cedd57fe95f994dc7b33`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260822T004959Z/inputs/blind_dossier.md` (`8d9eb971c14b4fab410ede5bffcd01af73db206f005a3152e5258263da69e26b`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260822T004959Z/inputs/blind_review_packet.md` (`8d9eb971c14b4fab410ede5bffcd01af73db206f005a3152e5258263da69e26b`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260822T004959Z/inputs/declaration_dossier.md` (`92e3a6b531eaf242e3c552e8073f16ae6857e68f7c9c1bb7499534f65fa40be4`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260822T004959Z/inputs/dependency_inventory.json` (`4a82dffbc55730e415038cfd3080f8f7367902acd622434b3feb1463c5b6ae1a`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260822T004959Z/inputs/direct_review_packet.md` (`c658e9eba0d9decddadbbbd12bfae052c8dbe8cf49074e67f7106a4bbd3c2211`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/history/20260822T004959Z/inputs/source_locator.json` (`a3919e68aedc0c649dc78dbd09686fa20956374216ce17671ed9c29eb8d34f46`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/blind_dependency_inventory.json` (`7a0ec63b411d5298535566e45eaeafc6df01d120f707637599aa0237faf8978a`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/blind_dossier.md` (`45a61adbae5924f97437be9c374cf7d76ed690db43d5bd4d5ea9538ee1ef71e9`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/blind_review_packet.md` (`45a61adbae5924f97437be9c374cf7d76ed690db43d5bd4d5ea9538ee1ef71e9`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/declaration_dossier.md` (`5b24c8455ed92ec7e02ca3797694a9550f986a12f8941acd54d28bd9ffbf7b4d`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/dependency_inventory.json` (`4135f1fcbe8217f00a0a1bef9ed8dc3c1ae05c20af8436464afcf736090f69ed`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/direct_review_packet.md` (`5ba484d00132f80bcbe73780a26686171b97d50125002decb78650d32b4fb022`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/source_locator.json` (`75e3f221aaf71e9ad2abdab996037f606bf419f70ab7492dc0d49679d3309820`)
