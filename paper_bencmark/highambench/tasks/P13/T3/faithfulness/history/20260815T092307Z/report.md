# Faithfulness audit: P13-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `8db574b332d0dc56d66172e9ae059af46ee2f0cb349590ad0491284501241cf4`
- Paper SHA-256: `9ebf8adb699f96c82ccbb153dd6ca592c64475a8bc3e0703a50cb659b012c520`

## Decision

The exact quotient and condition-number definitions contain algebraic forms that can represent the paper after choosing coeff j=w_j/(x-x_j). Likewise, paper counters could induce Lean additive perturbations with epsilon values chosen as suitable gamma bounds. Those choices and derivations are not part of the proposition. The target instead proves a nonvacuous, exact, generic perturbation inequality with an additional smallness premise. It omits the algorithm, floating-point model, operation-count constants, O(u^2) formulation, degree indexing, and sharpness claim. Because the Lean statement does not entail the complete paper result and the specialized paper theorem does not entail Lean's universal generic theorem, the relationship is different rather than equivalent, stronger, or merely weaker.

## Implications

- **Lean implies paper:** `no`. The Lean proposition alone supplies no barycentric coefficient construction, rounding execution, 3n+4 or 3n+2 counters, relationship between epsilon values and u, O(u^2) statement, or existential sharpness. Those missing facts are required to recover the complete paper result.
- **Paper implies lean:** `no`. The cited paper result concerns outputs of a specific barycentric floating-point algorithm. It does not assert the Lean theorem's universal finite inequality for every real coefficient array and every pair of arbitrary additive perturbations satisfying the generic predicates.

## Findings

- **critical / algorithm-linkage:** The proposition proves a generic quotient perturbation lemma rather than a theorem about the paper's algorithm.
- **major / constants-and-higher-order-terms:** The displayed Lean bound cannot be identified directly with either the exact counter model or Theorem 4.1's stated asymptotic bound.
- **major / conclusion-omission:** A substantive conclusion of the selected paper result is absent.
- **major / binders-and-indexing:** Recovering the paper setting requires an unstated parameter shift and external constructions, so the formal statement does not preserve the paper's binder semantics.
- **critical / algorithm-and-numerical-model:** The translated theorem does not state a result about the paper's algorithm.
- **critical / conclusion-and-higher-order-treatment:** The principal conclusion is replaced by a related but logically different perturbation lemma.
- **major / binders-dimensions-and-indexing:** The paper's dimension convention and essential mathematical objects are not preserved.
- **major / hypotheses-and-quantifiers:** Neither statement logically implies the other without substantial additional premises and derivations.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `pass` |
| `S07` | `fail` | `pass` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `38` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `38` dependencies (`22` hash-reused interpretations); failing or unclear: `D001, D005, D007`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/agent_outputs/blind_translation.json` (`5415f28c58508e5c70e8986e0ff99391c0d7f2a40e3713491707d78e17685f54`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/agent_outputs/direct_judge.json` (`a160ee6a7efb0b5d274d820c2b883d82404d76d47ee465ede0648f8db69f07fe`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/agent_outputs/paper_source_contract.json` (`0b665a5c91e976eec5d015b1b58ea8cec5aa3023d351689e493b8b019f9b8393`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`ea921b01be2b2f1de681e5bd1e4f1073da9f9520d571caa6ec7c6ea1b7c3c01f`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/agent_outputs/source_contract.json` (`1fd9df97b061759f96f83fd660ddf45bb41e6817ad39dd16101f2a2a8e4c9991`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/decision.json` (`66df4af900649f01e6a7aa81226f1723a169fdbaef5c98c9f26d57990ef50910`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/inputs/blind_dependency_inventory.json` (`cd883fe849044fc30c3208844f82a59b227acac018ae7ec5b74b0f2ec49ae96d`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/inputs/blind_dossier.md` (`f5e8dadbbc1d7f3992108cb38c4302c09faaf7f255a94073b469e9d93a14eb14`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/inputs/blind_review_packet.md` (`f5e8dadbbc1d7f3992108cb38c4302c09faaf7f255a94073b469e9d93a14eb14`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/inputs/declaration_dossier.md` (`46f9f0036236e0c7ef1cbd9cc3e88c9e7b0d2bae757a6a1a215a9a19f65383d0`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/inputs/dependency_inventory.json` (`2249b2efec86ff286a16333d5b0bc6e39b17f3d6144e6adde14a4dc3f188c7f8`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/inputs/dependency_reuse_direct.json` (`5fd765fc49342502b4ede143576255ac8f0ac012c362a3b01f3370504b0efebf`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/inputs/direct_review_packet.md` (`758f33d8f47f21a93300f14ff299c0f84946c8df33d3d93ee5b45a25efb25bb7`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/inputs/paper_source_locator.json` (`ec1d43325cb06b3c0839afb1c4848208a4c9dfd1b54b19aa5048fb5de3fa9f0f`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/inputs/source_locator.json` (`cbd7354e603aef1ff5912909ceea5085953d4dbe5a28ae4b8c52e6007bf7885c`)
