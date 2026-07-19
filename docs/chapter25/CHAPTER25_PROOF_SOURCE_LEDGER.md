# Higham Chapter 25 Proof-Source Ledger

| Source item | Chapter proof status | External source named by Higham | Local use |
|---|---|---|---|
| Local exact Newton convergence | Citation for standard quadratic convergence | Ortega and Rheinboldt, cited as [333], Thm. 5.2.1 | Only the exact Newton equation is modeled; no imported convergence claim. |
| Theorem 25.1 | Proof omitted; “See” citation | Tisseur (2001), §2.2 | Exact premises are modeled; ambiguous conclusion is deferred. |
| Theorem 25.2 | Proof omitted; “See” citation | Tisseur (2001), §2.3 | Ambiguous conclusion is deferred. |
| Eigenproblem symbolic specialization after (25.10) | Precise bordered Jacobian, Lipschitz, nonsingularity, and residual-evaluation prose followed by an experiment | Tisseur (2001) context | OPEN SELECTED: the decimal MATLAB run is excluded, but the four preceding exact symbolic claims require source-facing producers. |
| Linear-system specialization and condition identity | Direct prose and displayed formulae | Chapter 12 residual analysis | Closed locally by `higham25_linearSystem_newtonCorrection_iff_refinementCorrection`, `higham25_linearSystemJacobian_lipschitz_zero`, `higham25_linearSystem_actualResidual_bridge_ch12`, `higham25_linearSystemDataDerivativeFrob_eq`, and `higham25_linearSystem_condition_frobenius`; the source's Jacobian sign typo is corrected. |
| First-order structured stability discussion | Citation-based | Wozniakowski (1977) | The symbolic example, literal rounded evaluator, (25.13) producer, first-order algebra, and literal feasible supremum are formalized. Equation (25.11) is closed locally: Mathlib's implicit-function theorem supplies the local unique solution map, and `higham25_implicitFunction_hasFDerivAt` proves derivative `-F_x⁻¹ F_d`; `higham25_eq25_11_of_implicitFunction` proves the printed endpoint. The external citation is contextual, not a proof dependency. |
| Rheinboldt `C(F,S)` discussion | Citation-based and under-specified | Rheinboldt (1976) | DEFER-MISSING-PRECISE-STATEMENT; no diagonal/noncompact max/min semantics are invented. |
| Rigorous residual/error constants | Proof omitted; cited lemma, hypotheses not printed precisely | Kelley (1995), Lemma 4.3.1 | DEFER-MISSING-PRECISE-STATEMENT. |
| Problem 25.1 | Appendix proof printed | Descloux (1963) attribution | Appendix (A.15) and all mathematical conclusions are proved locally. |
| Problem 25.2 | Research prompt | Griewank (1985), Ypma (1983) | Excluded research problem. |

No Lean theorem is justified solely by an external citation.
