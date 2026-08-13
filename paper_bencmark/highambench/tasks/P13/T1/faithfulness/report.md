# Faithfulness audit: P13-T1

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `9c331535dfca807cb7a0aae7523f78ebad9de6564b9a9e66d0762cf08fd12892`
- Paper SHA-256: `9ebf8adb699f96c82ccbb153dd6ca592c64475a8bc3e0703a50cb659b012c520`

## Decision

Primary evidence confirms that P13-T1 includes both an exact identification of a perturbation-defined componentwise relative condition number and its lower bound by one. Lean retains only the quotient inequality. Although Lean syntactically allows arbitrary coefficient tuples, that does not supply genuine additional strength: every such nonzero finite product family can be represented by suitable paper interpolation data, so the paper entails Lean after the explicit cardinality reparameterization. Lean cannot entail the omitted condition-number identity. The implication pattern is therefore paper_implies_lean=yes and lean_implies_paper=no, which requires classification as not-faithful-weaker.

## Implications

- **Lean implies paper:** `no`. Specializing Lean's arbitrary ell to Lagrange basis values yields the quotient lower bound, but the Lean proposition contains no perturbations, supremum, limit, or independently defined condition number. It therefore cannot establish the paper's central equality between the perturbation-defined cond(x,n,f) and the quotient.
- **Paper implies lean:** `yes`. Let the Lean dimension be N>0 and write a_i=ell(i)f(i). Choose N distinct real interpolation nodes and an evaluation point different from every node, so each Lagrange value L_i(x) is nonzero. Set the paper data g_i=a_i/L_i(x). Then p_g(x)=sum_i a_i and sum_i |L_i(x)g_i|=sum_i |a_i|. The Lean nonzero hypothesis makes p_g(x) nonzero, and Lemma 2.2 yields the Lean inequality. For N=0, the Lean signed sum is the empty sum zero, so its hypothesis is impossible. The off-by-one parameter convention is handled by taking paper degree N-1, or by padding with zero data if a positive degree is required.

## Findings

- **critical / omitted-condition-number-identity:** The principal conditioning theorem is absent; only its elementary triangle-inequality consequence remains.
- **major / implication-direction:** The paper does imply every nonvacuous Lean instance, so the arbitrary ell binder does not create genuine stronger content or make the propositions incomparable.
- **minor / indexing:** This changes the parameter's meaning but is an ordinary reparameterization for positive Lean dimensions, not an obstruction to paper_implies_lean.
- **note / nonvacuity:** The weaker classification reflects genuinely omitted theorem content, not merely vacuity or reduced applicability.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `fail` |
| `S07` | `pass` | `pass` |
| `S08` | `not-applicable` | `not-applicable` |
| `S09` | `fail` | `fail` |
| `S10` | `fail` | `fail` |
| `S11` | `not-applicable` | `not-applicable` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `27` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `27` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D003, D005, D015, D017`.

## Remaining uncertainties

- The selected paper passage does not explicitly declare the scalar field, although its real-valued sign maximizer supports the Lean choice of Real; this does not affect the classification.
- Definition 2.1 prints epsilon tending to zero without separately specifying a one-sided limit; Lean omits the entire perturbation definition, so this ambiguity does not affect either implication verdict.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/agent_outputs/adjudicator.json` (`8b4c80d79acc17d34ccf1f484dd7b284dc0efb5996ee01f2abfec4722d589b46`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/agent_outputs/blind_translation.json` (`f388a6ceb3b2ef4963a9621ec489d775bdf564e51ff544f0c80f3a88c36599be`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/agent_outputs/direct_judge.json` (`ce5c37f0a333fb2e4c581c8af5c1760897d63f3f8966dbcb593ab88609dadc00`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/agent_outputs/paper_source_contract.json` (`0b665a5c91e976eec5d015b1b58ea8cec5aa3023d351689e493b8b019f9b8393`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`1e75c100e88a5082ada5643b10759f74d1f3dbaedfce182fcee345602db67f18`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/agent_outputs/source_contract.json` (`01737035b27887ac47bf9adfa541d023ce70271a101a5eac76bdccd160d1304f`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/decision.json` (`6ea8121cb207ba6d546d5e30e964a78655eeb64323a56d75d9076e20ddd1e7e0`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/inputs/blind_dependency_inventory.json` (`d648384163dd5cae777c1421fe58b2164efa2857c313fa103f7bbb41b8b7716b`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/inputs/blind_dossier.md` (`b565729e119a95bb3180eff990e59dfef2876db46a0f9ec7bf1a0f54d19e1a4e`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/inputs/blind_review_packet.md` (`b565729e119a95bb3180eff990e59dfef2876db46a0f9ec7bf1a0f54d19e1a4e`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/inputs/declaration_dossier.md` (`7955bf90e349ac89b265190322972436709a5b97383ef901e8e001fc4db26e77`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/inputs/dependency_inventory.json` (`3497ce0b70ebc4747f764d3e75800d4711c183dca27c9bd5f10abe92a6f39408`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/inputs/direct_review_packet.md` (`731f7b5c3b812eef504dd38891a9b7ef8059677d83bf48c5171022ab615aa70b`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/inputs/paper_source_locator.json` (`ec1d43325cb06b3c0839afb1c4848208a4c9dfd1b54b19aa5048fb5de3fa9f0f`)
- `paper_bencmark/highambench/tasks/P13/T1/faithfulness/inputs/source_locator.json` (`6a5a07bd54eb34d3b14eec73c9ab60b51908b60fac71f167061bd961c3e3802d`)
