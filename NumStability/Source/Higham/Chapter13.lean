import NumStability.Source.Higham.Chapter13.BlockLU
import NumStability.Source.Higham.Chapter13.DemmelSharpMultiplier

/-!
# Higham Chapter 13

Canonical declaration-free Chapter 13 aggregate. It re-exports the 69-owner
`Chapter13.BlockLU` source surface: Algorithms 13.1, 13.3, and 13.4; equations
(13.1)--(13.26); the numbered theorem, lemma, problem, and Table 13.1
families--together with the independent `DemmelSharpMultiplier` leaf. This
cutover covers the former `Algorithms.LU.BlockLU` owner; sibling migration
remains separate.
-/
