# W10 routing

All 1029 declarations of the 27 frozen owners are routed to the 43 destinations
authorized by B0012, or retained. B0012's frozen tier labels were treated as evidence to
review rather than permission to move whole files: all 27 owners were re-derived at
declaration level from the Lean sources, and 14 of them carry the
`mixed_pending_split` label that forbids wholesale classification outright.

| quantity | value |
| --- | ---: |
| declarations | 1029 |
| retained | 132 |
| relocated | 897 |
| to reusable `Algorithms/NormEstimation` | 492 |
| to source `Source/Higham/Chapter15` | 405 |
| populated destinations | 43 of 43 |
| reusable-to-source declaration edges | 0 |
| canonical-to-historical declaration edges | 0 |

Retention is **132**, exactly the private reverse-closure floor. Nothing is retained
beyond the floor: every declaration outside the closure proved relocatable.

## Tier rule and how it was enforced

Reusable carries generic norm and condition-estimation mathematics; source carries exact
Chapter 15 correspondence. Source may depend on reusable; reusable may never depend on
source, and no canonical module may depend on a declaration left in a historical owner.

Those two properties are not asserted, they are computed over the frozen P0013 edge set
after routing, and the first pass was **not** clean: 11 reusable-to-source edges survived
the initial declaration-level review. B0012 offers three remedies. Extraction of a neutral
prerequisite was unavailable, because every offending target is a printed endpoint --
Lemma 15.2 and its rectangular form, and the Boyd stationarity and derivative results --
which must remain source by definition. So the second remedy applied: the dependent
declaration was demoted to source, iterated to a fixpoint because demoting one strands its
reusable consumers.

The fixpoint took 5 iterations and 22 demotions:

| iteration | offending edges | declarations demoted |
| --- | ---: | ---: |
| 1 | 11 | 8 |
| 2 | 8 | 7 |
| 3 | 4 | 4 |
| 4 | 5 | 3 |
| 5 | 0 | fixpoint |

The demotions are coherent rather than scattered: the rectangular Boyd development
collapses onto `S:Lemma02/PNormPowerMethod` because it genuinely rests on printed
Lemma 15.2, and the concrete local-linearity results onto
`S:Section02/Boyd/SourceDomain`. Full per-declaration detail, including what forced each
demotion, is in `DECLARATION_ROUTES.tsv` (`demoted` column).

## Authorized but unpopulated destinations

None: all 43 authorized destinations are populated.
