# P09-T2 paper context

## Fixed source

The source is George U. Ramos (1971), *Roundoff Error Analysis of the Fast
Fourier Transform*. The local PDF SHA-256 is
`9076fe377cc64878a4a10f8a47ff49245bc5acaf116ffbd8e2ccca57033da758`.

The selected result is the prose construction and unnumbered displayed bounds
on PDF page 12, printed page 768, section 6.

## Local context and statement

Ramos treats an output error as the exact Fourier transform of a fictional
input perturbation. The real-equivalent Fourier matrix is `sqrt N` times an
orthogonal matrix. The target exposes that algebra at an arbitrary positive
scale: construct the perturbation by the scaled transpose, recover the output
exactly, obtain its Euclidean scaling law, and retain the max-norm certificate.
