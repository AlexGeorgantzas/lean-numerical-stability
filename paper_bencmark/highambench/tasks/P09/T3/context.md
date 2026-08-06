# P09-T3 paper context

## Fixed source

The source is George U. Ramos (1971), *Roundoff Error Analysis of the Fast
Fourier Transform*. The local PDF SHA-256 is
`9076fe377cc64878a4a10f8a47ff49245bc5acaf116ffbd8e2ccca57033da758`.

The selected result is Theorem 2(a) and its telescoping proof, especially
equation (4.2), on PDF page 8, printed page 764, section 4.

## Local context and statement

The paper decomposes multidimensional FFT error into the finite sum of local
errors propagated through preceding transforms. Each propagated term has a
first-order RMS budget plus an `O(epsilon^2)` remainder. The target replaces
the asymptotic notation by explicit per-term remainders and proves the exact
finite sum bound with the same leading coefficient `epsilon * sum K_i`.
