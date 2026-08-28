# P09-T1 paper context

## Fixed source

The source is George U. Ramos (1971), *Roundoff Error Analysis of the Fast
Fourier Transform*. The local PDF SHA-256 is
`9076fe377cc64878a4a10f8a47ff49245bc5acaf116ffbd8e2ccca57033da758`.

The selected result is the unnumbered maximum-versus-RMS inequality in the
proof of Theorem 1(b), PDF page 7, printed page 763, section 3.

## Local context and statement

For the output error vector `e`, Ramos observes that its largest squared
coordinate is bounded by the sum of all squared coordinates. With RMS defined
as Euclidean norm divided by `sqrt n`, this gives
`max(e) <= sqrt(n) * rms(e)`. The target states exactly this finite norm bridge.
