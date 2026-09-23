# Pilot 27 corpus-screen notes (not an admission record)

These are post-Pilot-26 development observations against the exact frozen
NumStability source commit `45813a95dacf577461bae13f033af0dbc985a225`.
They do not alter the launched three-task canary or retroactively remove any
previous task. They prevent an apparent library benefit from being credited
to retrieval of the complete target result in a later corpus.

| Legacy candidate | Source/library check | Current disposition |
|---|---|---|
| H5-5 | `NumStability/Algorithms/Horner.lean` defines `fl_rootProductEval` and proves `fl_rootProductEval_forward_error_bound` with `gamma (2*roots.length)` for the same rounded root-product algorithm. The packet asks for the weaker `gamma_(2n+1)` error bound. | Exclude from new component-not-result corpus unless a domain/algorithm difference is independently established. |
| H23-6 | `NumStability/Source/Higham/Chapter23/ThreeMStrassen/FirstOrder.lean` proves `higham23_threeMStrassen_sourceCoefficient` for the actual combined evaluator with the source's `6*c_Strassen+4` first-order coefficient and an explicit remainder. | Exclude: the target result is substantially present under another name. |

These checks are lexical plus statement inspection, not a full semantic
collision audit. Other candidates still need their own source, representation,
and target-collision gates. In particular, topical declaration names or an
import alone are insufficient to establish usable overlap.
