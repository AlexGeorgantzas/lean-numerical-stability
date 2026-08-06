# P19-T3 context

Sources: the right-preconditioned envelope (3.17) on physical PDF page 11 (printed page 10), the flexible-preconditioned envelope (3.20), and Remark 4 on physical PDF page 12 (printed page 11).

The right implementation reapplies the preconditioner when forming the solution approximation, whereas the flexible implementation stores its preconditioned basis. The two displayed bounds therefore share the `ug` and `ua` terms, while the right envelope has the additional `um * etaR * kappa(MR)` term.

The target defines exact paper-scoped operator-2 condition-number products, proves that the flexible envelope is no larger, identifies the exact gap, characterizes equality by vanishing of one gap factor, and proves strict improvement when all three factors are positive. This comparison concerns the displayed envelopes, not the actual errors or iteration counts.
