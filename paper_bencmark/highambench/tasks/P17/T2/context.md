# P17-T2 context

Source: equations (4.1)--(4.6) and Theorem 4.1 on PDF page 13 (journal page B1239), with its proof on B1240.

Equation (4.4) writes the computed recursive sum as each input multiplied by a suffix product. Theorem 3.6 bounds the expectation of each such product. The target exposes those expectations as `factor i`; if every effective factor differs from one by at most `gamma`, the relative bias is at most `gamma` times the paper's summation condition number.

Instantiating `gamma` with `p17Gamma (n-1) u_{p+r}` gives equation (4.6). Keeping the factor envelope explicit separates the paper-specific stochastic step from the exact condition-number calculation.
