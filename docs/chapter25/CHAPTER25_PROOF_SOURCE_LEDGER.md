# Higham Chapter 25 Proof-Source Ledger

| Source item | Chapter proof status | External source named by Higham | Local use |
|---|---|---|---|
| Local exact Newton convergence | Citation for standard quadratic convergence | Ortega and Rheinboldt, cited as [333], Thm. 5.2.1 | Only the exact Newton equation is modeled; no imported convergence claim. |
| Theorem 25.1 | Proof omitted; “See” citation | Tisseur (2001), §2.2 | Exact premises are modeled; ambiguous conclusion is deferred. |
| Theorem 25.2 | Proof omitted; “See” citation | Tisseur (2001), §2.3 | Ambiguous conclusion is deferred. |
| Eigenproblem experiment | Empirical | Tisseur (2001) and MATLAB components | Excluded empirical row. |
| First-order structured stability discussion | Citation-based | Wozniakowski (1977) | The symbolic example, literal rounded evaluator, (25.13) producer, first-order algebra, and literal feasible supremum are formalized. `higham25_eq25_11_of_actualSolutionMap_hasFDerivAt` proves the Taylor-to-limit step from a genuine Fréchet derivative, but the source's implicit-function producer from smooth `F` and nonsingular `F_x`, including derivative `-F_x⁻¹ F_d`, is still open. Equation (25.11) is therefore **PARTIAL**, not citation-backed closure. |
| Rheinboldt `C(F,S)` discussion | Citation-based and under-specified | Rheinboldt (1976) | DEFER-MISSING-PRECISE-STATEMENT; no diagonal/noncompact max/min semantics are invented. |
| Rigorous residual/error constants | Proof omitted; cited lemma, hypotheses not printed precisely | Kelley (1995), Lemma 4.3.1 | DEFER-MISSING-PRECISE-STATEMENT. |
| Problem 25.1 | Appendix proof printed | Descloux (1963) attribution | Appendix (A.15) and all mathematical conclusions are proved locally. |
| Problem 25.2 | Research prompt | Griewank (1985), Ypma (1983) | Excluded research problem. |

No Lean theorem is justified solely by an external citation.
