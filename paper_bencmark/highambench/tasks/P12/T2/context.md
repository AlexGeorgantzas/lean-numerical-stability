# P12-T2 paper context

## Fixed source

The source is Marko Lange and Shin'ichi Oishi (2020), *A note on Dekker's
FastTwoSum algorithm*. The local PDF SHA-256 is
`0569d969cebaabe42de69fef10fa91002af12d62149af7485d0712414b53c2a1`.

The selected result is Theorem 2, including equations (3), (7), and (8), on
PDF pages 5--6 / printed pages 387--388. Equation (1), the rounding
definitions, and the original three-line FastTwoSum algorithm are on PDF page
2 / printed page 384; the multiple-representation convention is explained on
PDF page 3 / printed page 385.

## Floating-point system

`P12RadixFormat` records an arbitrary integer radix `beta >= 2`, positive
mantissa length `p`, and inclusive exponent range `[emin, emax]`.
`P12Representation fmt x` is a particular equation-(1) witness

```text
x = m * beta^e,
-beta^p < m < beta^p,
emin <= e <= emax,
```

where `m` and `e` are integers. Representations are intentionally not
normalized or unique. `p12Representable fmt x` says that at least one such
witness exists; it does not select a preferred exponent.

`p12RadixGeometry fmt` proves the general radix-grid consequences of equation
(1) used in the paper's proof: rebasing a sufficiently small representable
number, bounded exact addition and subtraction as in equation (8), the local
nearest-rounding bound for equal exponents, and the exponent increase forced by
the complementary large-sum case. These are derived for every admissible
`P12RadixFormat`; they are not additional target hypotheses. In particular,
neither subtraction performed by the selected execution is assumed exact or
representable.

## Algorithm and rounding

`P12FastTwoSumExecution fmt x y tr` is exactly the original algorithm:

```text
s = nearest(x + y)
t = faithful(s - x)
e = faithful(y - t).
```

Nearest rounding minimizes absolute distance over the equation-(1) set.
Faithful rounding permits either adjacent endpoint and fixes no tie rule, but
allows no other representable value between the returned endpoint and the
exact result. Every rounded output therefore belongs to the same `F`.

Equation (8) is explicitly qualified by "in the absence of overflow," although
Theorem 2 does not separately list that hypothesis. The execution therefore
records range validity for the exact sum and both exact differences using the
strict upper endpoint `beta^p * beta^emax`. This resolves the source ambiguity
without assuming representability of either difference. Equation (1) contains
finite real values and zero; there are no infinities, NaNs, exception flags, or
signed-zero distinction. The theorem imposes no separate underflow exclusion.

## Condition and conclusion

Both ordered inputs `x` and `y` belong to `F`. The theorem retains condition
(7) in its original existential form: some permitted representation of `x`
must satisfy

```text
|y| <= (beta^p - beta/2) * beta^e(x).
```

The proof obtains a representation of `y` with `e(y) <= e(x)` and follows the
paper's three cases. It uses the equation-(8) grid criterion to establish, not
assume, the two exact computed identities

```text
t = s - x,
e = y - t.
```

The fixed conclusion exposes both identities, the exact error-free transform
`s + e = x + y`, and the nearest-addition property
`|s - (x + y)| <= |y|`. All operations on the right sides are exact real
operations. No first-order approximation, hidden cross term, or big-O term is
used.
