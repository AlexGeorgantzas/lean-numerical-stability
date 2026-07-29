# P02-T1 paper context

## Fixed source

The source is Takeshi Ogita, Siegfried M. Rump, and Shin'ichi Oishi,
*Accurate Sum and Dot Product*, 2005. The local file is
`paper_bencmark/reference_papers/ACCURATE SUM AND DOT PRODUCT.pdf`. Its SHA-256
hash is `e7b8523c793ad7345dfc76f681c44d1afbbc3a810fb948912451432ae616512d`.

The target is equation (4.7)(i) and Algorithm 4.3 (`VecSum`) on PDF page 11,
printed page 1965, in section 4, "Summation." The local error-free identity it
uses is equation (3.2) in Theorem 3.4 on PDF page 8, printed page 1962.

## Small amount of local context

`TwoSum(a,b)` returns a high component `x` and a low component `y`. The
error-free contract says

`x + y = a + b`.

`VecSum` starts with the first input as its high component. It combines each
later input with the current high component using `TwoSum`, saves the emitted
low component, and continues with the new high component. Its output consists
of all saved low components followed by the final high component.

The Lean target writes a nonempty vector of paper length `N` as
`Fin (n+1) -> Real`, so `N = n+1`. The shared `vecSum` definition implements
exactly the cascade above. The shared `ErrorFreeAddModel` contains the standard
rounded-addition rule and the three local `TwoSum` properties needed by all P02
tasks. This target itself needs only local exactness.

## Informal theorem statement

The exact sum of the vector produced by one `VecSum` pass equals the exact sum
of the input vector.

## Informal proof from the paper

At one cascade step, `TwoSum` replaces the current high component and the new
input by two numbers with the same exact sum. Therefore that step does not
change the total of the saved low components, the current high component, and
all inputs not yet processed. Repeating the identity through the vector leaves
the original exact sum equal to the sum of every emitted low component plus the
final high component. This is equation (4.7)(i).

## Fixed Lean target

The exact checked statement is `p02_t1_vecSum_preserves_sum` in `Target.lean`.
Every name in it comes from mathlib or the shared `HighamBench` file, and the
same statement and shared setting are used in conditions N and L.
