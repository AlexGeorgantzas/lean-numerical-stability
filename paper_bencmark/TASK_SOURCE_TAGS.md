# Source tags for paper tasks

Each HighamBench task records how the selected result is presented by the
paper. This is separate from the T1/T2/T3 tier and separate from Lean's use of
the `theorem` command.

## Allowed tags

| Tag | Use it when |
| --- | --- |
| `THM` | The paper explicitly labels the selected result “Theorem.” |
| `LEM` | The paper explicitly labels the selected result “Lemma.” |
| `PROP` | The paper explicitly labels the selected result “Proposition.” |
| `COR` | The paper explicitly labels the selected result “Corollary.” |
| `EQN` | The selected result is given as a numbered equation or formula. |
| `TXT` | Essential part of the selected result is stated only in prose. |
| `UNL` | The selected result is displayed but has no number or named label. |

## Assignment rules

- Tag the selected task result, not all supporting material used by its proof.
- An explicitly named result receives exactly its named tag. Record the exact
  printed label in `author_label`, for example `"Proposition 4.5"`.
- For a result without a named label, `author_label` is `null`.
- `EQN` may be combined with `TXT` when prose materially specializes or
  completes the numbered formula.
- Keep the list in the order shown in the table and do not repeat tags.
- Preserve exact PDF-page, printed-page, section, and equation evidence in
  `source_locations`.
- Assign and review tags whenever a task is created or revised. All paper IDs
  use this same construction workflow.
- A task remains editable while the benchmark is under construction. A later
  measurement-ready snapshot records the exact version used for runs.

## Current assignments

| Task | Source tags | Author label | Reason |
| --- | --- | --- | --- |
| `P01-T1` | `EQN`, `TXT` | none | Equation (3.6), completed by the paper's prose about nonnegative inputs. |
| `P01-T2` | `EQN`, `TXT` | none | Equations (2.6) and (3.6), completed by the following prose comparison. |
| `P01-T3` | `EQN` | none | The selected result is given by equations (5.1)--(5.3). |
| `P02-T1` | `EQN` | none | The selected invariant is equation (4.7)(i); Theorem 3.4 is supporting material. |
| `P02-T2` | `PROP` | `Proposition 4.5` | The paper explicitly names the selected result. |
| `P02-T3` | `PROP` | `Proposition 5.11` | The paper explicitly names the selected result. |
| `P03-T1` | `EQN` | none | The selected result is equation (4.1). |
| `P03-T2` | `THM` | `Theorem 4.1` | The paper explicitly names the selected result. |
| `P03-T3` | `THM` | `Theorem 5.1` | The paper explicitly names the selected result. |
| `P04-T1` | `EQN`, `TXT` | none | Algorithm 3.1 and equations (3.1)--(3.4), completed by the surrounding compact factorization and evaluation-order discussion. |
| `P04-T2` | `THM` | `Theorem 3.2` | The paper explicitly names the selected result. |
| `P04-T3` | `THM` | `Theorem 4.4` | The paper explicitly names the selected result. |
| `P05-T1` | `LEM` | `Lemma 4.1` | The paper explicitly names the selected result. |
| `P05-T2` | `THM` | `Theorem 4.2` | The paper explicitly names the selected result. |
| `P05-T3` | `THM` | `Theorem 4.4` | The paper explicitly names the selected result. |
| `P06-T1` | `EQN` | none | The selected result is equation (4.20), with its inherited Theorem 4.4 event and hypotheses retained. |
| `P06-T2` | `EQN` | none | The selected result is equation (3.4), represented in equivalent all-threshold form. |
| `P06-T3` | `EQN` | none | The selected product expansion is given by equations (4.8)--(4.9). |
| `P07-T1` | `LEM` | `Lemma 3.2` | The paper explicitly names the selected strict-perturbation rank result. |
| `P07-T2` | `UNL` | none | The selected exact backward-error expansion and norm step are displayed but unnumbered inside Theorem 3.5's proof. |
| `P07-T3` | `LEM` | `Lemma 2.1` | The paper explicitly names the selected condition-number identity. |
| `P08-T1` | `LEM` | `Lemma 4.2` | The selected forward-error inequality is one of the two explicit conclusions of Lemma 4.2. |
| `P08-T2` | `LEM` | `Lemma 4.2` | The selected residual-image inequality is the other explicit conclusion of Lemma 4.2. |
| `P08-T3` | `LEM` | `Lemma 4.3` | The selected finite residual recurrence is the induction content of Lemma 4.3. |
| `P09-T1` | `UNL` | none | The selected max-versus-RMS formula is displayed but unnumbered in the proof of Theorem 1(b). |
| `P09-T2` | `TXT`, `UNL` | none | Prose asserts the fictional input perturbation and the following unnumbered displays give its norm bounds. |
| `P09-T3` | `THM` | `Theorem 2` | The selected multidimensional RMS bound is explicitly named Theorem 2(a). |
| `P10-T1` | `EQN` | none | The selected inherited-right-input amplification term is part of equation (8). |
| `P10-T2` | `EQN` | none | The selected product-error rule is equation (8), with its suppressed cross term made explicit in the finite formalization. |
| `P10-T3` | `EQN`, `TXT` | none | The displayed recurrence and equation (20) are completed by the following prose conclusion that SylR is logarithmically stable. |
| `P11-T1` | `EQN` | none | The selected first-column residual estimate is equation (16). |
| `P11-T2` | `UNL` | none | The selected exact defect identity is displayed but unnumbered in the proof of Theorem 1(7). |
| `P11-T3` | `THM` | `Theorem 1` | The selected loss-of-orthogonality bound is the explicit conclusion (7) of Theorem 1. |
| `P12-T1` | `EQN` | none | The selected nearest-addition error property is equation (10). |
| `P12-T2` | `THM` | `Theorem 2` | The selected error-free transform is Theorem 2, with equations (3), (7), and (8) providing its certificate form. |
| `P12-T3` | `LEM` | `Lemma 4` | The selected exact ThreeProduct identity is Lemma 4, equation (18). |
| `P13-T1` | `LEM` | `Lemma 2.2` | The selected result is Lemma 2.2's exact identification of Definition 2.1's condition number with equation (2.2), together with its lower bound. |
| `P13-T2` | `LEM` | `Lemma 2.2` | The selected componentwise data-perturbation bound is the second explicit conclusion of Lemma 2.2. |
| `P13-T3` | `THM` | `Theorem 4.1` | The selected result is Theorem 4.1's two-condition-number bound, retained `O(u^2)` term, and sharpness sentence, with the preceding exact perturbed quotient supplying its execution model. |
| `P14-T1` | `EQN` | none | The selected aggregate positive-sum result is equation (3.3); the preceding unnumbered exponential and recursive-summation displays supply its execution and proof context. |
| `P14-T2` | `THM` | `Theorem 3.3` | The selected basic-softmax componentwise bound is explicitly named Theorem 3.3. |
| `P14-T3` | `EQN`, `TXT` | none | Equation (1.4) supplies shift invariance and the paper later uses exact normalization and nonnegative mass in prose. |
| `P15-T1` | `TXT` | none | Section 2.1 states Frobenius submultiplicativity in prose as the first norm property used throughout the analysis. |
| `P15-T2` | `LEM` | `Lemma 3.1` | The selected truncation-plus-rounding backward-error result is explicitly named Lemma 3.1. |
| `P15-T3` | `THM` | `Theorem 4.5` | The selected BLR linear-system backward-error result is explicitly named Theorem 4.5. |
| `P16-T1` | `UNL` | none | Section 2 gives the selected minimum normwise backward-error identity in an unnumbered display. |
| `P16-T2` | `LEM` | `Lemma 4.2` | The selected exact identity and first-order restarted residual recurrence are the backward-error half of Lemma 4.2. |
| `P16-T3` | `THM` | `Theorem 6.3` | The selected mixed-precision contraction and attainable-floor result is explicitly named Theorem 6.3. |
| `P17-T1` | `THM` | `Theorem 3.6` | The selected corrected finite-probability product envelope remains explicitly tied to Theorem 3.6; the project-added sign conditions are documented separately. |
| `P17-T2` | `THM` | `Theorem 4.1` | The selected recursive-summation bias bound is explicitly named Theorem 4.1. |
| `P17-T3` | `THM` | `Theorem 4.3` | The selected variance-based probabilistic summation bound is explicitly named Theorem 4.3. |
| `P18-T1` | `TXT`, `UNL` | none | The prose following equation (3.3) introduces the selected exact split, and the split itself is displayed without a number. |
| `P18-T2` | `TXT`, `UNL` | none | The selected corrected-midpoint arrays and cancellation certificate are unnumbered displays introduced and interpreted in prose; numbered conditions (3.4)-(3.5) supply the general order-condition definitions instantiated by the certificate. |
| `P18-T3` | `TXT`, `UNL` | none | Section 4.3 introduces Method 4s3pC and its regularity distinction in prose; the selected certificate uses the unnumbered coefficient and following error-form displays. |
| `P19-T1` | `EQN` | none | The selected upper perturbation-norm inequality is the right half of equation (C.8). |
| `P19-T2` | `THM` | Theorem 3.1 | The selected result is Theorem 3.1, including equations (3.7)-(3.8) and the four-source definition of `xi`. |
| `P19-T3` | `EQN`, `TXT` | none | Equations (3.17) and (3.20) give the two envelopes, and Remark 4 identifies the removed preconditioner-reapplication term. |
| `P20-T1` | `EQN`, `TXT` | none | Equations (3.1), (3.2), and (3.4a) give the diagonal scaling, threshold, and interval; prose requires power-of-two factors and states the maximum-coefficient consequence. |
| `P20-T2` | `EQN` | none | The selected complete scaled-input rounding and underflow bound is equation (3.13). |
| `P20-T3` | `THM` | Theorem 4.1 | The selected result is Theorem 4.1: equations (4.29)-(4.31) define the scaled p-word computation and (4.32) gives its narrow-range normwise forward-error bound; (4.33) supplies the range-free comparison. |

These assignments are ordinary task metadata. They follow the same rules and
may be reviewed in the same way for every paper entry during construction.
