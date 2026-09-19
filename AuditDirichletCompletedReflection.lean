import AnalyticNumberTheory.Dirichlet.GammaFactorRegularity
import AnalyticNumberTheory.Dirichlet.CompletedReflection

/-!
# Completed Dirichlet-L reflection trust audit

Focused kernel audit for the neutral positive-half-plane gamma regularity,
completed-functional-equation extraction, and regular-point ordinary-L logarithmic-derivative
reflection consumed by downstream GRH projects. CI enforces the repository axiom whitelist
exactly.
-/

#print axioms AnalyticNumberTheory.Dirichlet.differentiableAt_Gammaℝ_of_re_pos
#print axioms AnalyticNumberTheory.Dirichlet.gammaFactor_ne_zero_of_re_pos
#print axioms AnalyticNumberTheory.Dirichlet.differentiableAt_gammaFactor_of_re_pos
#print axioms AnalyticNumberTheory.Dirichlet.symmetricCompletedLFunction_one_sub
#print axioms AnalyticNumberTheory.Dirichlet.logDeriv_symmetricCompletedLFunction_one_sub
#print axioms AnalyticNumberTheory.Dirichlet.logDeriv_symmetricCompletedLFunction_eq_three_factors_of_regular
#print axioms AnalyticNumberTheory.Dirichlet.logDeriv_LFunction_eq_reflected_of_regular
