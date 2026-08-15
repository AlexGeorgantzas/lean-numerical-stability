# Faithfulness audit: P10-T2

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `f56d9d29c88782c5d68a355e935a7fe695114305d019209ecfb4438dc36ff3a4`
- Paper SHA-256: `0ee818d060542baefdd85cbb7c7f2fd948efcb927101da84c37e418713f87269`

## Decision

The PDF directly supports a local, absolute normwise first-order product-error rule. The Lean packet correctly models real square operands, exact multiplication, a compatible norm, and the three displayed budget terms; its local equation (1) certificate is legitimate modularization and does not assume equation (8), and the complete recursive inversion algorithm is unnecessary. The decisive mismatch is the bounded object and asymptotic scope. Lean bounds computedProduct-AB-DeltaA*DeltaB-remainder exactly, while the paper accounts for the actual computed-product error modulo uniformly higher-order effects. The run contains no epsilon-indexed inherited-error families, its higher-order coefficient can depend on the fixed epsilon and remainder, and its mu witnesses are run-local. Consequently cross and remainder deletion can hide arbitrarily large actual error, even allowing arbitrary computed outputs to satisfy a run certificate. Neither implication holds, so this is a different, non-faithful proposition rather than a stronger theorem or an acceptable specialization.

## Implications

- **Lean implies paper:** `no`. From the Lean run one can at most derive an actual-error bound equal to the displayed budget plus leftInheritedError*rightInheritedError and higherOrderCoeff*epsilon^2. With no epsilon-uniform first-order inherited errors or uniform coefficient, those additions are not O(epsilon^2), so the paper's first-order actual-error rule does not follow.
- **Paper implies lean:** `no`. The paper gives an asymptotic scalar bound for a stable multiplication execution; it does not assert the Lean theorem's universal exact decomposition or control the specifically truncated matrix after independently chosen cross and remainder terms. Possible cancellation also prevents an actual-error bound from implying a bound on an arbitrarily selected component.

## Findings

- **critical / different-error-object:** The formal inequality can hold while the actual computed-product error is arbitrarily larger than equation (8)'s budget.
- **critical / nonuniform-higher-order-semantics:** The perturbation cross term need not be quadratic, and any finite discrepancy can be labeled higher order at one positive epsilon.
- **major / algorithm-and-mu-quantifier-scope:** The theorem does not establish a uniform stable multiplication routine or its algorithm-level growth contract.
- **note / faithful-local-structure:** The local algebra, norm semantics, coefficient placement, real specialization, and omission of the full recursive inversion algorithm are individually appropriate.
- **critical / bounded-error-object:** The proposition concerns a different error object and does not directly bound the computed product's full forward error.
- **major / first-order-uniformity:** The removed cross product can be leading order or arbitrarily large, so its omission is not justified as a higher-order omission.
- **major / higher-order-remainder:** The remainder certificate does not represent a uniform big-O term and places no meaningful higher-order control on the asserted error.
- **major / coefficient-dependence:** The formal scope loses the fixed algorithm-wide dependence needed for the paper's stability model.
- **note / local-certificate-modularization:** This part is noncircular and is a legitimate local abstraction; the complete recursive inversion algorithm is not required.
- **note / norm-and-domain:** These choices are acceptable for the local equation and are not the source of rejection.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `pass` | `pass` |
| `S07` | `fail` | `pass` |
| `S08` | `fail` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `pass` | `pass` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `fail` |
| `S14` | `fail` | `fail` |
| `S15` | `pass` | `pass` |
| `S16` | `fail` | `pass` |

## Dependency coverage

- Blind translator covered `66` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `66` dependencies (`0` hash-reused interpretations); failing or unclear: `D002, D004, D011, D012, D013, D014, D015, D016, D017`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/agent_outputs/blind_translation.json` (`ad8f3eb4a664ba0e61f090092bd821930adc2071585f00ee4b031d6bc272237b`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/agent_outputs/direct_judge.json` (`bcdd26e2770193a9b58bf34adcf777cce3e28a4794bb03932390ea2f5655268e`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`91178079cd9c357be1e63028919496f99d6c6c6e35c79a1e58df2115969f04f8`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/agent_outputs/source_contract.json` (`69ec8f212638421b4a01df40f662c4a884d0d95bdc01f447ec4b18764bd14c41`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/decision.json` (`503a87c2d191945b478c1adc08bd63c0db647f512ef29707be89f73a2b67230a`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/agent_outputs/blind_translation.json` (`559f6d1e96571c9877d952afdb42bb8205c09e30f049a44ad67792352c5349b1`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/agent_outputs/direct_judge.json` (`e1a6926a52d5959da1ec2961bb1a850dd23a43ffbdf53c5d7d88d2e52828f281`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/agent_outputs/paper_source_contract.json` (`a730fdcbbc543ec8712373b135d8a67dd310f31f635dedabf0ed548f9316414a`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/agent_outputs/roundtrip_judge.json` (`59f2c179c5302184cc13a03b919bf67f4b7b663c34b3f02f1b52663194f5885b`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/agent_outputs/source_contract.json` (`af7fa355c5dade9d76fb53f107b3b32ff7103edf0361110875f740f9baa89612`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/decision.json` (`f2015fec1b645d07a2ffc467365b70355e6084c9c2a0a11410c33ac7ff7a9dde`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/inputs/blind_dependency_inventory.json` (`0392614de25d2d2adb2289c0b1899389997494470f2547e1d2c288816cfe5641`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/inputs/blind_dossier.md` (`e81fdd6586663abfd118de175147ad1ef6bc5345b5051f82c59672ee854b1a4c`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/inputs/blind_review_packet.md` (`e81fdd6586663abfd118de175147ad1ef6bc5345b5051f82c59672ee854b1a4c`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/inputs/declaration_dossier.md` (`b333917c31f30480fac3efff76052e6fe2d1a1c8556d546f577c184170017b05`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/inputs/dependency_inventory.json` (`f15473cf9706a022eda818c8973023b7e87fff3b5fb42b24be69ec4b51714a74`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/inputs/dependency_reuse_direct.json` (`a91219164d34d309cc938ea3b63b91bd83b570c3801ccd20d74c69f6a3afe938`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/inputs/direct_review_packet.md` (`d497f433a129b9c8ae7effd6171e0d1c5fdbcf93487c3d83c51e84f131eca76f`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/inputs/paper_source_locator.json` (`91f77a26c65c7ca024e216f6cc35327e6521963eee50d0bda4fd50b72060a4dc`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/inputs/source_locator.json` (`5024d15fffb84de9174802e1e04a0124e7961850131b58b3ca4190f0248a1ed8`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/blind_dependency_inventory.json` (`78b55c122ea7f4e7cae7fa95eac0faa913b593e365f3cb611dbd7c407a747236`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/blind_dossier.md` (`588f3a61a1c9d9a6aa9e908b220c9f05abdcd699b967d25e943c2a9080826e9f`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/blind_review_packet.md` (`588f3a61a1c9d9a6aa9e908b220c9f05abdcd699b967d25e943c2a9080826e9f`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/declaration_dossier.md` (`ca35e7d825093f0a244f30607161e168d1af74a2ec416bef8a06b185554c7497`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/dependency_inventory.json` (`ed2a072c67791456bd4d84fbfc2fab101db00bfeaa5b39831dda2b1352266f5d`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/direct_review_packet.md` (`0159e798ef6db7fba59f235354245d82517b9b920e04f916ddfb741d22b84f21`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/source_locator.json` (`5024d15fffb84de9174802e1e04a0124e7961850131b58b3ca4190f0248a1ed8`)
