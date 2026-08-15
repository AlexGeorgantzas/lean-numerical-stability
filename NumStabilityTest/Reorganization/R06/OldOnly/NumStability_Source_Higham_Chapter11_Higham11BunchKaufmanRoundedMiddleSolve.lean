import NumStability.Source.Higham.Chapter11.Higham11BunchKaufmanRoundedMiddleSolve

/-!
# R06 historical-only test — `Higham11BunchKaufmanRoundedMiddleSolve`

Imports exactly the historical path; checks its preserved public
surface (3 declarations).
-/

#check @NumStability.Higham11RoundedBunchKaufmanExecution.MiddleSolveRunDomain
#check @NumStability.Higham11RoundedBunchKaufmanExecution.actualMiddleSolve_backward_error
#check @NumStability.Higham11RoundedBunchKaufmanExecution.gamma_one_le_thirtySix_mul_u_of_gammaValid_nine
