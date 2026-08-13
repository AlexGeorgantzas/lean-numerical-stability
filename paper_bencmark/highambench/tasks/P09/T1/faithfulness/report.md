# Faithfulness audit: P09-T1

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `false`
- Target SHA-256: `b03593f5fdfd9c0eedb5ab88bfc5c86b371d2b941ea63942e6e1511fff220bea`
- Paper SHA-256: `9076fe377cc64878a4a10f8a47ff49245bc5acaf116ffbd8e2ccca57033da758`

## Decision

After unfolding every target dependency, the Lean statement is max_i |e_i| <= sqrt(n) * (sqrt(sum_i e_i^2)/sqrt(n)) for every positive n and real vector e. This matches the exact conversion displayed in the proof of Theorem 1(b). The paper's complex error vector is covered by instantiating Lean with its component magnitudes, and the RMS formulations are equal for n > 0. Lean removes algorithm-specific context and quantifies over all real vectors, which is genuine, satisfiable extra generality; the paper's fixed FFT-error instance does not imply that universal proposition. Hence the result is accepted as faithful-stronger, with no unclear dependency or semantic check requiring adjudication.

## Implications

- **Lean implies paper:** `yes`. Given the paper's positive order N and complex output error e(i) = fl(y(i)) - y(i), instantiate Lean with the real vector r(i) = |e(i)|. Then p09Max r is max_i |e(i)| and p09Rms r is sqrt(sum_i |e(i)|^2)/sqrt(N), equal to the paper's RMS norm. The Lean conclusion is exactly the selected paper conversion.
- **Paper implies lean:** `no`. The selected passage asserts the conversion for the particular complex output-error vector arising in the enclosing FFT computation. It does not quantify over every arbitrary real vector or show that every such vector is realizable as an FFT output error. Therefore that paper-context instance alone does not imply Lean's universally quantified proposition.

## Findings

- **note / specialization/generalization:** The target is broader, not narrower: applying it to the real vector of complex component magnitudes recovers the paper result, while its universal real-vector statement is not supplied by the paper-context instance.
- **major / binder-and-scope generalization:** The translation is not a literal restatement, but it is nonvacuously stronger and entails the paper's norm inequality by applying it to component magnitudes.
- **major / algorithm-and-error linkage:** The proposition loses the provenance and intended application of e, although those omissions do not weaken the exact algebraic inequality.
- **note / norm and constant preservation:** The core norm semantics, dimension, indexing, non-strict relation, and coefficient are preserved exactly.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `pass` | `fail` |
| `S04` | `pass` | `pass` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `fail` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `not-applicable` | `not-applicable` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `fail` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `36` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `36` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P09/T1/faithfulness/agent_outputs/blind_translation.json` (`ddd651280f0f3d2c83f26a8691fe8de80ad59172f4b987bd03805f5a7409d52d`)
- `paper_bencmark/highambench/tasks/P09/T1/faithfulness/agent_outputs/direct_judge.json` (`0c5ca0bd579e0000ccfaef9cedba92d65e70b845241634e65be4ee03dbab9856`)
- `paper_bencmark/highambench/tasks/P09/T1/faithfulness/agent_outputs/paper_source_contract.json` (`348db3c4cffe4770d8510e9fec47ccdab62bf40c19935e431854786ba7f44db4`)
- `paper_bencmark/highambench/tasks/P09/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`46eb692b4b796d19c1f3ae05868323c2d0a4173ca5c27d2d599287afeb946a68`)
- `paper_bencmark/highambench/tasks/P09/T1/faithfulness/agent_outputs/source_contract.json` (`a33248a5b40082e00f056c255f66a9f1fa72f15f94a7c97a24e573a58ca7b393`)
- `paper_bencmark/highambench/tasks/P09/T1/faithfulness/decision.json` (`caac1e667a5c2d1fe84ac323a34b830d7c3c43b5eaa227e2b60b41711b80b411`)
- `paper_bencmark/highambench/tasks/P09/T1/faithfulness/inputs/blind_dependency_inventory.json` (`9ffe84bf07d23e13c2597bcd1363e67e27857be5eea4a942dbc280e2d02d80e7`)
- `paper_bencmark/highambench/tasks/P09/T1/faithfulness/inputs/blind_dossier.md` (`8aa8c74838d289cc9d2845e87499ea512ad6791656f406fcddf24b03452b85ac`)
- `paper_bencmark/highambench/tasks/P09/T1/faithfulness/inputs/blind_review_packet.md` (`8aa8c74838d289cc9d2845e87499ea512ad6791656f406fcddf24b03452b85ac`)
- `paper_bencmark/highambench/tasks/P09/T1/faithfulness/inputs/declaration_dossier.md` (`fea5451ac2a44b23d1cc6260927ce36833081a91959eaa2cbd0fb57751aa62a2`)
- `paper_bencmark/highambench/tasks/P09/T1/faithfulness/inputs/dependency_inventory.json` (`4a04766e90252632a51d97b77fd7415555fb1a9ded6547b94c6f1e8059d3f3de`)
- `paper_bencmark/highambench/tasks/P09/T1/faithfulness/inputs/direct_review_packet.md` (`723a6d179bb99f10cc9c71c5f0fb76e66f99821583b79e73d5d36d6e8a388f32`)
- `paper_bencmark/highambench/tasks/P09/T1/faithfulness/inputs/paper_source_locator.json` (`f236078d56116000664fec27c570812daeb11eb5024aaf78838800ecc07f8a13`)
- `paper_bencmark/highambench/tasks/P09/T1/faithfulness/inputs/source_locator.json` (`b5141d9c9b06736a651b55499dd2aec49b855a6d924b57b74949a9df2e12e796`)
