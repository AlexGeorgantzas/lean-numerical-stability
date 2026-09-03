import NumStability.Source.Higham.Chapter01.Section03.ErrorSources.All

/-! COMP-02 declaration-bearing isolation check for `NumStability.Source.Higham.Chapter01.Section03.ErrorSources.All`.

Imports exactly one module and exercises a representative public
declaration reachable through it. The declaration is provided by
`NumStability.Source.Higham.Chapter01.Section03.ErrorSources.Core`; a break in the forwarding chain makes this file fail.
-/

#check @NumStability.ErrorSource.chapterOneMainSource_exhaustive
