import NumStability.Source.Higham.Chapter20.Theorem07.RowPolicy

/-!
# Theorem07.RowPolicy canonical-only import smoke test

Imports exactly one canonical module so no sibling import can supply
the declarations checked below.
-/

#check @NumStability.Higham20RowSorting.exactQ
#check @NumStability.Higham20RowSorting.exactR
#check @NumStability.Higham20RowSorting.exactASeq
