# Faithfulness audit: P09-T2

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `aa4cb42146660670f9e5c335e3bc2f335aaffb801ddf9a14e0b47bbcbf997540`
- Paper SHA-256: `9076fe377cc64878a4a10f8a47ff49245bc5acaf116ffbd8e2ccca57033da758`

## Decision

The Lean proposition is a valid, nonvacuous theorem about preimages under arbitrary positively scaled real orthogonal matrices. It captures an abstract analogue of the exact equation and norm-scaling idea, but it changes the complex Fourier operator to a generic real operator, leaves the scale unbound, treats e as arbitrary, and omits both first-order roundoff bounds and their higher-order terms. Consequently neither statement implies the other as stated, so the result is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. The Lean theorem does not establish that its operator is the paper's complex Fourier matrix, that e is an FFT roundoff error, or either epsilon- and K-dependent certificate. Even a realification and s = sqrt(N) instantiation would require unstated links and would not supply the omitted bounds.
- **Paper implies lean:** `no`. The paper asserts a result for its fixed complex Fourier transform and FFT-generated errors. It does not assert the universal theorem for every dimension, real orthogonal Q, arbitrary real e, and arbitrary positive scale s.

## Findings

- **critical / missing-error-certificates:** The principal quantitative content of the selected result is absent.
- **major / transform-and-scalar-domain:** The formal theorem does not directly cover the paper's operator or vector space.
- **major / algorithm-linkage:** The backward-error statement is detached from the computation whose roundoff error the paper analyzes.
- **major / norm-and-scale-semantics:** Only an abstract norm-preserving preimage fact remains; the displayed paper norm certificates are not represented.
- **critical / missing-error-certificates:** The central roundoff and backward-stability content is absent, so the translation cannot imply the paper result.
- **major / operator-and-type-substitution:** Ordinary real transpose and real coordinate norms do not directly represent the complex Fourier transform, making the statements semantically different.
- **major / algorithm-and-error-model-erasure:** The translated statement loses both the algorithmic scope and the intended forward-to-backward error interpretation.
- **major / norm-and-scaling-mismatch:** No binder equates s with sqrt(N), and the translated infinity relation does not express the paper's certificate.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `fail` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `fail` | `fail` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `48` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `48` dependencies (`32` hash-reused interpretations); failing or unclear: `D001, D002, D003, D004, D005, D006, D007, D008, D009, D020, D034, D035, D036, D037`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/agent_outputs/blind_translation.json` (`9a01b41ec8fa4ec0e535babdd26a23ee9a254c5f2dddfb4022347fd85e10b48f`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/agent_outputs/direct_judge.json` (`96e78149d5f1527bcd14ba3d9f5b7302e081e4abddcf5c375b589344af1c2fa8`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/agent_outputs/paper_source_contract.json` (`348db3c4cffe4770d8510e9fec47ccdab62bf40c19935e431854786ba7f44db4`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`9190ac3f562ba1bc4dec035015ef2d9fc9e99c35b8b4c8a660907fb300386c68`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/agent_outputs/source_contract.json` (`9c13c3b7713e9414917faa07e430b9762c89eac6389542ad64fb6e6cde3b71cf`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/decision.json` (`dcbf463d44cb8cd08a983a971074340b78b8ec27ac824248040c367018bf8860`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/blind_dependency_inventory.json` (`fc3d3b7c6cc18275d3502b928f52a741e0d7b858f2df29fa7b73355926baff9f`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/blind_dossier.md` (`7362b410440afdb0f170536e029a4b7f4950420491d462b75eece22df2864539`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/blind_review_packet.md` (`7362b410440afdb0f170536e029a4b7f4950420491d462b75eece22df2864539`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/declaration_dossier.md` (`4989f464acf809a1a315eef2165312f2f768aa23e432dce8df6721c74c3b1231`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/dependency_inventory.json` (`7007e3f10524bf3ca95fd2979e8ac87518a05d64722301654960172e0e7894cb`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/dependency_reuse_direct.json` (`057fba236f94854071eebfb32df89c84b8b2e73381c348e7cce2c5072f9b010a`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/direct_review_packet.md` (`bc0ee1b457543e8af14569c5fe21f98ced94c30a2af87e2414147e9646211e59`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/paper_source_locator.json` (`f236078d56116000664fec27c570812daeb11eb5024aaf78838800ecc07f8a13`)
- `paper_bencmark/highambench/tasks/P09/T2/faithfulness/inputs/source_locator.json` (`fe2bf8a9e74bbce7778ab97cec39a1da3ac1e48456b0cc88c60f8fb8978f3a3b`)
