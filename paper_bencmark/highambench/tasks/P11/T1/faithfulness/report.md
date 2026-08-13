# Faithfulness audit: P11-T1

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `ce563f7e0fd0548b6c559904eba5a7710896861762c06917f37de966cecf59f8`
- Paper SHA-256: `72b7521848be07971a6721ea0356bb898c63e21b8ad3aa109fee8f41517284a5`

## Decision

Primary inspection shows that the selected source is the k=1 induction base of Theorem 1 for computed CGS-P factors, not a free-standing theorem about arbitrary matrices. Its perturbation is algorithm-dependent, bounded in the induced spectral norm, and tied by exact equalities to the computed first-column residual under inherited floating-point and conditioning assumptions. Lean instead proves an exact universal Frobenius-to-Euclidean action inequality and omits the perturbation construction, residual identities, computed quantities, algorithm, source dimensions, and numerical model. A Frobenius premise is narrower than the paper's spectral premise and does not make the complete Lean statement a faithful strengthening. Independent checks of both implication directions therefore give no/no, yielding not-faithful-different with accepted=false.

## Implications

- **Lean implies paper:** `no`. The Lean theorem proves only a universal action inequality under a Frobenius-norm premise. It does not supply the computed perturbation witness, q1 normalization relation, residual identities, CGS-P execution, or inherited hypotheses. Moreover, the paper gives only ||G1||_2<=epsilon_M, which need not imply ||G1||_F<=epsilon_M.
- **Paper implies lean:** `no`. The paper's result is restricted to the perturbation and first column arising from each admissible computed CGS-P run. It does not quantify over every square real G and every vector a, and its spectral-norm premise is not Lean's Frobenius-norm premise.

## Findings

- **critical / proposition-replacement:** The formal target is a supporting generic action lemma, not the selected first-column residual result.
- **critical / matrix-norm-mismatch:** The source perturbation need not satisfy the Lean premise with coefficient one, so Lean cannot be instantiated to recover the paper bound.
- **major / quantifier-and-algorithm-mismatch:** Witness dependence, computed status, and algorithm linkage are lost, preventing implication in either direction.
- **major / missing-source-context:** The target does not state when the paper's perturbation and residual arise and cannot be treated as a faithful stronger theorem merely because its explicit binder list is broader.
- **minor / dimensions-and-domain:** The operator action can be dimensionally aligned by mapping Lean n to paper m, but the original problem dimensions and nondegenerate domain are not represented.
- **note / matching-local-fragment:** This local algebraic resemblance does not overcome the norm, quantifier, residual, and algorithmic mismatches.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `fail` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `pass` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `fail` | `fail` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `pass` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `31` dependencies; unclear: `none`.
- Direct judge covered `31` dependencies; failing or unclear: `D002, D008`.

## Remaining uncertainties

- The paper does not specify whether G1 is diagonal or give its entries; only its action relation and spectral-norm bound are source-guaranteed.
- The paper does not specify the exact IEEE rounding mode or behavior outside the normalized range, so no more detailed exceptional-value contract can be recovered from the cited text.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/agent_outputs/adjudicator.json` (`6dd477313776e9b16971fc243e4725e56a9cede70fa53b11d4d961f767dd50a7`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/agent_outputs/blind_translation.json` (`33d631145d9171c5a10d906e00f5f2e935108c805144e36cfec487b50b447365`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/agent_outputs/direct_judge.json` (`8fb8d336e29a399b7e6d914ceeef9f05405de6a11d229888e240f8ee6e6b2d2f`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`1a723fb7ea84b892619076684ca6192e360e13c40472b643678643bd76409bdd`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/agent_outputs/source_contract.json` (`b6b205e2131601bc1e987c77ba6a94a5fe0519814e45a8898036c7da6d23f3ba`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/decision.json` (`4f63dd898137c097064ef7cbfdcbc1d0d426207f0ecff9b9038045ea2c7d3c0f`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/blind_dossier.md` (`1b49b7fd0dbd315f2767a43f76cab9d60a7d713a1084e882569d4f887bb4d682`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/declaration_dossier.md` (`781435c9386bfcdaf7fc38e1b9355f040381a48b6da9929294395c2565203738`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/source_locator.json` (`e19ebf9ab8fdeca1573b78753863b04c548b278b0ff6e3071e560bcd5dd72c70`)
