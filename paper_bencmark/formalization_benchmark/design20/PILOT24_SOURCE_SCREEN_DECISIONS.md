# Pilot 24 source-screen decisions before measurement

The original priority and reserve order was frozen in
`PROSPECTIVE_12_SCREEN.md` before Pilot 23's first paired verdict. The original
`CORPUS_12_CANDIDATE.json` is retained unchanged. These decisions are based on
independent source-only review of the PDF and packet, not on N/L task outcomes.

## Rump Theorem 4.3: exclude

The source reviewer at
`/hdd/alexgeorgantzas/highambench/pilot24-source-review-RUMP12-THM4.3-20260923-a`
marked the packet `unclear` because the **printed strict first inequality is
false** for an allowed input. In binary64 round-to-nearest-even, use n=1,
`x₁ = η` (the smallest positive subnormal) and `y₁ = 1/2`. Their exact product
is `η/2`, which rounds to zero. Both computed accumulators are zero, so
`ufp(Ŝ)=0`; the exact absolute error and the proposed right-hand side are
both `η/2`. The source asserts `<`, not `≤`. The `(n+2)u≤1` guard holds.
The packet correctly represented the printed result, but the result is not a
sound benchmark target. No silent nonzero or no-underflow restriction is
permitted. Preserve the reviewer artifact and exclude this task. The first
pre-ordered reserve is `CAST08-FIXED3`, pending its own source/admission gates.

## Rump Theorem 3.5: correct packet and re-review

The source-only reviewer at
`/hdd/alexgeorgantzas/highambench/pilot24-source-review-RUMP12-THM3.5-20260923-a`
found the packet omitted the paper's explicit `ufp(0)=0` convention. This
matters for all-zero inputs. It also documented that the paper's equality
witness uses ties-to-even, whereas the main inequalities permit any nearest
tie rule. The corrected packet states those quantifiers separately and
retains the paper's broad domain. It must receive a fresh independent review
with its new hash before admission. The reviewer also identified a possible
proof issue for asymmetric tie rules; the source result is not silently
narrowed to repair that argument.

## Rump Theorem 3.4: source packet accepted, not yet admitted

The source-only reviewer at
`/hdd/alexgeorgantzas/highambench/pilot24-source-review-RUMP12-THM3.4-20260923-a`
returned `faithful`: n≥1, representable inputs, nearest rounding, no
overflow, underflow allowed, and the unguarded exact `(n−1)u` factor are all
retained. It noted a minor strict-versus-nonstrict step in the published proof
at n=2, not a defect in the theorem statement. Direct component, collision,
and full-domain skeleton gates remain open.

## Packet corrections pending fresh source review

The first Langlois–Louvet Theorem 4 and 7 packet reviews found an unsupported
2007 bibliography year in the pinned PDF. Both packets now use the PDF's arXiv
v1 year 2006. The Theorem 7 reviewer additionally required the paper's
implicit `2nu<1` gamma-validity condition and positive degree; those are now
explicit. This does not weaken the selected criterion.

The first Castaldo Proposition 3.2 and fixed-three-level packet reviews
required the paper's explicit *no-underflow* assumption, correct Section 1.1
model location, and accurate pointer-reset wording. The Proposition 3.2 packet
now unambiguously selects the mathematical hierarchy supported by Section 3
prose, Figure 3.2, and Proposition 3.1 rather than the plainly defective
Figure 3.1(a) carry loop. It may only be admitted if a fresh independent
review accepts that interpretation. The printed program defect and a separate
problem in the paper's supporting error-counter algebra remain disclosed.

## Task-neutral retrieval vocabulary correction

The off-benchmark candidate-V2 preflight exposed only `FPModel` and `gamma`
for FAB19-EQ3.6, despite the frozen library containing the exact lower-level
`fl_recursiveSum` and `fl_kahanSum` algorithms. The router recognized
“recursive block” but missed “recursive working-precision block”, and had no
family for the ordinary phrase “compensated accumulation”. Before any Pilot 24
contestant ran, the router gained those generic aliases and the public
`fl_kahanSum` anchor. It also maps “superblock dot product” to the existing
two-level `fl_blockDotProduct` component, never to the unproved three- or
t-level target. These additions are applied to the frozen atlas by the same
rule for every task; they are not task-ID overrides or answer declarations.
The candidate-V2 preflight is diagnostic only and cannot serve as final
admission evidence after this code change or packet corrections.
