# P17-T1 context

Source: Theorem 3.6 on PDF page 9 (journal page B1235), continuing on B1236.

The paper proves that if the conditional mean of each stochastic rounding error is a bounded truncation error, then the expectation of the accumulated product lies between `(1-B)^n` and `(1+B)^n`. The target is its exact deterministic one-atom specialization: expectation becomes evaluation and the error equals its conditional mean. This preserves the product envelope without importing a probability model into the direct-use task.

The statement is finite, does not use asymptotic notation, and assumes `B <= 1` so every lower comparison factor is nonnegative.
