import AnalyticNumberTheory.Dirichlet.TwistedMangoldtPerron

/-!
# Twisted Mangoldt Perron core trust audit

Focused audit for the minimal project-neutral character layer needed before the
sharp character-Perron wrapper.  This includes the exact-same-pin untwisted
Mangoldt norm-series support plus the thin twisted coefficient/L-series adapter.
-/

#print axioms BombieriVinogradov.SiegelWalfisz.vonMangoldtLSeriesNormSum
#print axioms BombieriVinogradov.SiegelWalfisz.LSeriesTerm_vonMangoldt_eq_ofReal
#print axioms BombieriVinogradov.SiegelWalfisz.re_LSeriesTerm_vonMangoldt_eq_norm
#print axioms BombieriVinogradov.SiegelWalfisz.norm_LSeriesTerm_vonMangoldt_eq
#print axioms BombieriVinogradov.SiegelWalfisz.vonMangoldtLSeriesNormSum_eq_neg_logDeriv_re
#print axioms LiuWang.Proof.ExplicitPerron.psi_eq_sum_one
#print axioms LiuWang.Proof.ExplicitPerron.mangoldt_normSum_eq_norm
#print axioms LiuWang.Proof.ExplicitPerron.mangoldt_normSum_le
#print axioms AnalyticNumberTheory.Dirichlet.norm_twistedMangoldtSequence_le_vonMangoldt
#print axioms AnalyticNumberTheory.Dirichlet.neg_logDeriv_LFunction_eq_twistedMangoldtLSeries
#print axioms AnalyticNumberTheory.Dirichlet.twistedMangoldt_normSum_le
