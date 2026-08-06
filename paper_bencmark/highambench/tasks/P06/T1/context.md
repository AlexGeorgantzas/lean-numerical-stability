# P06-T1 paper context

## Fixed source

The source is Michael P. Connolly and Nicholas J. Higham (2023),
*Probabilistic Rounding Error Analysis of Householder QR Factorization*. The
local PDF SHA-256 is
`c02a20e9ffa8039a5ad3db9261fba19929de84bf0bff7654547541dffe496a79`.

The selected result is equation (4.20), PDF page 10, printed page 1155,
section 4.

## Local context and statement

Theorem 4.4 first gives the same relative Euclidean backward-error coefficient
for every column of the input matrix. The prose immediately before (4.20)
observes that these columnwise estimates imply a Frobenius-norm estimate with
the identical coefficient. The target isolates this exact deterministic
aggregation. Its parameter `η` represents the paper's leading probabilistic
coefficient; the separately discussed `O(u²)` contribution is outside this
finite exact implication.
