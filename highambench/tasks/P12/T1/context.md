# P12-T1 paper context

## Fixed source

The source is Marko Lange and Shin'ichi Oishi (2020), *A note on Dekker's
FastTwoSum algorithm*. The local PDF SHA-256 is
`0569d969cebaabe42de69fef10fa91002af12d62149af7485d0712414b53c2a1`.

The selected result is equation (10), PDF page 6, printed page 388, in
Section 3.

## Local context and statement

The proof of Theorem 2 isolates the only property needed from nearest
addition: the rounded sum is no farther from `x+y` than the representable
candidate `x`, hence its error is at most `|y|`. The target states this
nearest-representative argument independently of a particular radix format.
