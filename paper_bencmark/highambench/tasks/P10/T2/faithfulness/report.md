# Faithfulness audit: P10-T2

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `90fdf84b3b59fe01d3c2e850d61d4c50cf9d5c47195270fb1d7cea2379e37518`
- Paper SHA-256: `0ee818d060542baefdd85cbb7c7f2fd948efcb927101da84c37e418713f87269`

## Decision

The Lean proposition is a valid exact Frobenius-norm inequality for an unconstrained algebraic perturbation expansion. Equation (8), by contrast, is a first-order absolute normwise computed-error rule tied to stable multiplication, with a specified mu(n)*epsilon local term and exactly two inherited-error propagation terms. Because Lean neither constrains E nor connects dA and dB to inherited errors, and because it retains the omitted higher-order cross term, neither statement implies the other in the intended semantics. The result is therefore not-faithful-different, not a stronger formalization.

## Implications

- **Lean implies paper:** `no`. Lean places no upper bound on norm(E) by mu(n)*epsilon*norm(A)*norm(B), does not identify dA and dB with inherited errors, and retains a nonnegative cross term. Consequently its four-term generic bound cannot yield the paper's three-term first-order computed-error rule.
- **Paper implies lean:** `no`. The paper's first-order scalar accounting does not quantify arbitrary perturbation matrices or E, does not state the exact matrix expansion, omits dA*dB, and leaves the norm unspecified. The Lean inequality is independently true from algebraic norm properties, not a semantic consequence of equation (8).

## Findings

- **critical / missing-local-roundoff-model:** The target cannot establish the paper's local rounding-error budget or any floating-point stability claim.
- **major / different-error-object-and-higher-order-term:** The additional term makes the right side looser rather than stronger, and the exact perturbation lemma is not the paper's three-term rule.
- **major / missing-computation-and-algorithm-linkage:** The theorem holds independently of the numerical algorithm and therefore does not measure the claimed paper result.
- **minor / unsupported-norm-specialization:** This is a nontrivial real-matrix specialization, but it silently chooses norm semantics and factors not fixed by the source.
- **critical / numerical-model substitution:** The translation expresses a different mathematical result and neither statement semantically implies the other.
- **major / missing local-error factor:** The central machine-precision-dependent contribution cannot be recovered from the translated proposition.
- **major / higher-order mismatch:** The translation changes the error budget and weakens the upper bound by adding a quadratic contribution.
- **major / error-variable independence:** The proposition loses the semantic dependencies that make equation (8) an error-propagation statement.
- **minor / norm and domain specialization:** The translation silently narrows the domain and norm semantics beyond what the target passage specifies.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
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
| `S14` | `fail` | `fail` |
| `S15` | `pass` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `29` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `29` dependencies (`24` hash-reused interpretations); failing or unclear: `D002, D003`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/agent_outputs/blind_translation.json` (`559f6d1e96571c9877d952afdb42bb8205c09e30f049a44ad67792352c5349b1`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/agent_outputs/direct_judge.json` (`e1a6926a52d5959da1ec2961bb1a850dd23a43ffbdf53c5d7d88d2e52828f281`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/agent_outputs/paper_source_contract.json` (`a730fdcbbc543ec8712373b135d8a67dd310f31f635dedabf0ed548f9316414a`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`59f2c179c5302184cc13a03b919bf67f4b7b663c34b3f02f1b52663194f5885b`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/agent_outputs/source_contract.json` (`af7fa355c5dade9d76fb53f107b3b32ff7103edf0361110875f740f9baa89612`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/decision.json` (`f2015fec1b645d07a2ffc467365b70355e6084c9c2a0a11410c33ac7ff7a9dde`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/blind_dependency_inventory.json` (`0392614de25d2d2adb2289c0b1899389997494470f2547e1d2c288816cfe5641`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/blind_dossier.md` (`e81fdd6586663abfd118de175147ad1ef6bc5345b5051f82c59672ee854b1a4c`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/blind_review_packet.md` (`e81fdd6586663abfd118de175147ad1ef6bc5345b5051f82c59672ee854b1a4c`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/declaration_dossier.md` (`b333917c31f30480fac3efff76052e6fe2d1a1c8556d546f577c184170017b05`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/dependency_inventory.json` (`f15473cf9706a022eda818c8973023b7e87fff3b5fb42b24be69ec4b51714a74`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/dependency_reuse_direct.json` (`a91219164d34d309cc938ea3b63b91bd83b570c3801ccd20d74c69f6a3afe938`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/direct_review_packet.md` (`d497f433a129b9c8ae7effd6171e0d1c5fdbcf93487c3d83c51e84f131eca76f`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/paper_source_locator.json` (`91f77a26c65c7ca024e216f6cc35327e6521963eee50d0bda4fd50b72060a4dc`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/source_locator.json` (`5024d15fffb84de9174802e1e04a0124e7961850131b58b3ca4190f0248a1ed8`)
