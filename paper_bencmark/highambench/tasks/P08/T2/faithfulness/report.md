# Faithfulness audit: P08-T2

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `false`
- Target SHA-256: `2326a842839c910d167baf6efe557e185c684e97189ca2d0f7b92c00bbeee761`
- Paper SHA-256: `f520066b46331dcbf25e51345c5ff5ffffe8fcad573d7f46e68834f83b3a2c54`

## Decision

After unfolding all local definitions, the Lean conclusion is exactly the componentwise expansion of |A(x_{m+1}-x)| <= (I+u|A||A^{-1}|)|q_{m+1}|+u|A||x|. Every paper instance satisfies the Lean hypotheses. Lean weakens the contextual premises to the inverse action on q and the rewritten final-update relations, so it also covers additional non-algorithmic and some singular-matrix cases. That extra domain is satisfiable and genuine, making the proposition faithful-stronger rather than merely equivalent.

## Implications

- **Lean implies paper:** `yes`. Fix any paper iteration m>=0 and instantiate Ainv=A^{-1}, q=q_{m+1}, h=h_{m+1}, and xNext=x_{m+1}. Positivity gives hu; invertibility gives hInverseAction; the proof's equivalent update gives hUpdate and hRound. D001-D003 then turn the Lean conclusion into the paper's first Lemma 4.2 inequality component by component.
- **Paper implies lean:** `no`. The selected paper statement quantifies only algorithm-generated iterates for nonsingular A with the actual inverse and standing floating-point context. It does not, as a stated result, establish the Lean proposition for arbitrary A,Ainv,x,q,h,xNext satisfying only local action, update, and error inequalities, including non-algorithmic and some singular-matrix instances.

## Findings

- **note / genuine-domain-generalization:** The Lean proposition strictly generalizes the paper result while retaining it by direct instantiation; this supports faithful-stronger rather than equivalence.
- **note / floating-point-abstraction:** This broadens the algebraic theorem without changing the selected bound; no IEEE-specific claim or computed-residual identification is introduced.
- **major / algorithm-linkage-and-scope:** The translation is strictly more general, so the paper does not imply it as stated.
- **major / inverse-and-residual-semantics:** Generic translated instances lack the paper's exact-solution and residual meanings, although paper instances specialize into the translation.
- **major / floating-point-model:** The operational numerical model is abstracted away and the admissible parameter range is broadened.
- **minor / dimension-edge-case:** The translation adds a vacuous zero-dimensional case, but this does not account for its substantive strength on positive dimensions.
- **note / conclusion-fidelity:** Under the paper specialization, the targeted inequality is reproduced without altered constants, norms, directions, or omitted terms.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `pass` | `fail` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `fail` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `fail` |
| `S13` | `pass` | `fail` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `28` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `28` dependencies (`27` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P08/T2/faithfulness/agent_outputs/blind_translation.json` (`7ab1d93d5349eb056475ef539e12fdfbd08f5159974a4f44bf750a20a82c8922`)
- `paper_bencmark/highambench/tasks/P08/T2/faithfulness/agent_outputs/direct_judge.json` (`bb1fe28a44e37acf30e11b7b59367f756b8bdfef982b10e423760a2a65d64cfc`)
- `paper_bencmark/highambench/tasks/P08/T2/faithfulness/agent_outputs/paper_source_contract.json` (`a163817fa5c88f26c8ba3e26089da7681e1ce417d954cec7742e812dbcc3f006`)
- `paper_bencmark/highambench/tasks/P08/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`6ec300961f1139c38557bf10fc91af12b433c902ccd00d81adbe1ecb85bc1488`)
- `paper_bencmark/highambench/tasks/P08/T2/faithfulness/agent_outputs/source_contract.json` (`14e1ee7c06971470b5de1282bcdea04b248f9060a72d55623530c29c46040c21`)
- `paper_bencmark/highambench/tasks/P08/T2/faithfulness/decision.json` (`32459cfa160ac4c8f30a8339f001c08d95923d68cd11318293c732b4d63b2e58`)
- `paper_bencmark/highambench/tasks/P08/T2/faithfulness/inputs/blind_dependency_inventory.json` (`768de6c05e6c84017412e3e67fcc124d9a7d76677b1a5ab8f0e67c797be6c914`)
- `paper_bencmark/highambench/tasks/P08/T2/faithfulness/inputs/blind_dossier.md` (`555f9cd226dc5bd96cf0619cf9139d61109ee0d44b54d1b801c2f301f6ccb400`)
- `paper_bencmark/highambench/tasks/P08/T2/faithfulness/inputs/blind_review_packet.md` (`555f9cd226dc5bd96cf0619cf9139d61109ee0d44b54d1b801c2f301f6ccb400`)
- `paper_bencmark/highambench/tasks/P08/T2/faithfulness/inputs/declaration_dossier.md` (`72db8d405496a490d5124088b0788749b05e855153403c447abbbc220015c65f`)
- `paper_bencmark/highambench/tasks/P08/T2/faithfulness/inputs/dependency_inventory.json` (`2cff6e6d37ba37a7dbdec627e4de650978ba5647918d978f541a91beb4e32069`)
- `paper_bencmark/highambench/tasks/P08/T2/faithfulness/inputs/dependency_reuse_direct.json` (`aed47dcf8afa1e167aa29361c262b5715685053a3798133f234b599e3fad9a8f`)
- `paper_bencmark/highambench/tasks/P08/T2/faithfulness/inputs/direct_review_packet.md` (`223b014f1622922c7da07fbe4a67961321034587df15cf1f59f01fed6a7b7cee`)
- `paper_bencmark/highambench/tasks/P08/T2/faithfulness/inputs/paper_source_locator.json` (`3242b63a529acc04514175dadb3f98deebf67f847a6bf33be0b5bb7850f84391`)
- `paper_bencmark/highambench/tasks/P08/T2/faithfulness/inputs/source_locator.json` (`0571af9fc068f72ac147079cf04a52acc379a6220ffa3e27ce7edc39c7d859b8`)
