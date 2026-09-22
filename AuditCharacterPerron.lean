import AnalyticNumberTheory.Dirichlet.CharacterPerronClosedError
import AnalyticNumberTheory.Dirichlet.CharacterPerronResidue

/-!
# Sharp character Perron wrapper trust audit

Focused audit for the bounded actual-character wrapper over the integrated dyadic
Perron theorem and twisted von Mangoldt core, including the closed half-integer
central-cost bound and the real-endpoint local residue seam consumed by finite
contour shifts. No GRH or application premise is introduced by this slice.
-/

#print axioms AnalyticNumberTheory.Dirichlet.twistedMangoldtPartialSum
#print axioms AnalyticNumberTheory.Dirichlet.characterPerronIntegrand
#print axioms AnalyticNumberTheory.Dirichlet.characterPerronIntegrand_eq_series
#print axioms AnalyticNumberTheory.Dirichlet.characterPerronVertical_eq_series
#print axioms AnalyticNumberTheory.Dirichlet.norm_characterPerron_sub_partialSum_le
#print axioms AnalyticNumberTheory.Dirichlet.characterPerronClosedHalfError
#print axioms AnalyticNumberTheory.Dirichlet.centralCost_twisted_halfInteger_le_closed
#print axioms AnalyticNumberTheory.Dirichlet.norm_characterPerron_sub_partialSum_le_closed_halfInteger
#print axioms AnalyticNumberTheory.Dirichlet.residue_characterPerronIntegrand
