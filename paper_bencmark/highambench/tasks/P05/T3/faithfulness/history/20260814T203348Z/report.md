# Faithfulness audit: P05-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `c7f9b7ce7d229dbc4ad8209d2a2f863c20aab142c8417b57ca3c4c7392b1a760`
- Paper SHA-256: `dd8b525c0eabc509a68b325ee5008cf6f1d4ef262bef8ba54e1947fe3cdb3db6`

## Decision

The target correctly encodes the exact identity R^T R = A + DeltaA, the componentwise majorant |R^T||R|, and the zero-based forms of the rowwise (i+1)u and uniform (n+1)u constants. However, it removes the floating-point Cholesky algorithm and its execution assumptions and replaces the substantive upper-triangle error analysis by hupper. It also omits the distinct local estimates (4.5a)-(4.5b) and quantifies arbitrary real matrices. Consequently it is an algebraic symmetry-extension result with neither implication to the paper theorem, so it is not faithful.

## Implications

- **Lean implies paper:** `no`. The Lean statement cannot establish Theorem 4.4 from successful floating-point Cholesky execution because it contains no execution model and requires the central upper residual estimate hupper as an additional premise.
- **Paper implies lean:** `no`. The paper proves the conclusion only for computed floating-point Cholesky factors under its execution conditions; it does not assert Lean's universal algebraic implication for every arbitrary real A and R satisfying hupper.

## Findings

- **critical / algorithm-linkage:** The formal theorem does not prove the paper's numerical-stability result; it proves only an algebraic symmetry extension after the substantive estimate has been supplied.
- **major / floating-point-model:** The theorem ranges over a different class of objects and cannot express the paper's hypotheses.
- **major / local-estimates:** The distinct local bounds and the numerical derivation that produces them are missing.
- **major / quantifier-domain:** The two claims are logically incomparable rather than equivalent or a faithful strengthening.
- **critical / algorithmic result replaced by residual premise:** The proposition does not formalize the paper's substantive numerical-analysis claim.
- **major / floating-point execution model omitted:** The translated statement has no semantic connection to the conditions under which the paper proves its bound.
- **major / local estimates missing:** Required cases, constants, and algorithm-derived local information are lost.
- **major / unintended trivialization:** The formal result can be established without reasoning about Cholesky factorization or floating-point error.
- **note / core equation and full-bound constants preserved:** The algebraic form and componentwise interpretation of the main displayed conclusion are accurately represented despite the missing derivation and numerical context.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `pass` | `pass` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `37` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `37` dependencies (`30` hash-reused interpretations); failing or unclear: `D017`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/agent_outputs/blind_translation.json` (`cdc53949f20209460810b6aa91be140d279befb6c32d7f9151d394703bc0979a`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/agent_outputs/direct_judge.json` (`46e490112fdfb2957b85ba525c40a7a5e7c4f9d5f9e70e678f9755a9eb5af43d`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/agent_outputs/paper_source_contract.json` (`90bcb3f32112e46567a1fde6c0c742ef1d157d1829c1eb2b2cb5ebb4d58d4c1d`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`a9c106c7bf4879ef0f85cb589b3378cf208246afe75fff6eb20a15899071d4c0`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/agent_outputs/source_contract.json` (`383f9b21985e279369d4c14212bb70109146c948c8e3013af05eef6c69781b11`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/decision.json` (`25b9b204f5ba5c77aea814ca96ddd4abc589a5008896a1a5f00675bff904cf6e`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/blind_dependency_inventory.json` (`12bf0cd0f6f079664df24f38b8eb4a2637a07e24db008460622b072ef62e3744`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/blind_dossier.md` (`8740a5009980963200c72465c2c36a8d3c670689db7ea8e8a7ae7b8da369ccd8`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/blind_review_packet.md` (`8740a5009980963200c72465c2c36a8d3c670689db7ea8e8a7ae7b8da369ccd8`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/declaration_dossier.md` (`2deecf940f270dcc15e90e0e80eb3330f30d813342c5ca792ff28f3fa85710dd`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/dependency_inventory.json` (`9cce9ce2eb6ff22fbc5b06987ba96e0137ddcb05f4b7e2ff92c360b7bcb906eb`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/dependency_reuse_direct.json` (`80f198548bad495db52ce5b9d42a75abdd6bfc3e24d439720fb000cc6551f73b`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/direct_review_packet.md` (`6fc5702fd4006c8c0e8af8fbc28c745ee3c5a8516f4381145a0d2c1ae575126b`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/paper_source_locator.json` (`417f8e6a6ff934c35d3c2379d9faefe1c21d44b1f14a69f7674c0ef303123327`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/source_locator.json` (`9ec305a0bba44c4c7bb843aa8558ea4136ceb4e622b5321d0ee3125a78b54220`)
