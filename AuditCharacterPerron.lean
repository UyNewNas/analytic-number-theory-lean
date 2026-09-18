import AnalyticNumberTheory.Dirichlet.CharacterPerron

/-!
# Sharp character Perron wrapper trust audit

Focused audit for the bounded actual-character wrapper over the integrated dyadic
Perron theorem and twisted von Mangoldt core.  No GRH or application premise is
introduced by this slice.
-/

#print axioms AnalyticNumberTheory.Dirichlet.twistedMangoldtPartialSum
#print axioms AnalyticNumberTheory.Dirichlet.characterPerronIntegrand
#print axioms AnalyticNumberTheory.Dirichlet.characterPerronIntegrand_eq_series
#print axioms AnalyticNumberTheory.Dirichlet.characterPerronVertical_eq_series
#print axioms AnalyticNumberTheory.Dirichlet.norm_characterPerron_sub_partialSum_le
