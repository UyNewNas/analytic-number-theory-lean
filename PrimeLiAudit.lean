import AnalyticNumberTheory.PrimeDistribution.ChebyshevTheta

/-!
# Focused genuine-Li trust audit

This file keeps the genuine logarithmic-integral slice independently auditable
while the wider `dev` build has a separately tracked LargeSieve baseline failure.
The workflow checks these reports against the same standard axiom whitelist as
`Audit.lean`; this is an additional gate, not a replacement for the full audit.
-/

#print axioms AnalyticNumberTheory.PrimeDistribution.primeLogIntegral_two
#print axioms AnalyticNumberTheory.PrimeDistribution.primeLogIntegral_additive_normalization_sub
#print axioms AnalyticNumberTheory.PrimeDistribution.primeLogIntegral_nonneg
#print axioms AnalyticNumberTheory.PrimeDistribution.primeLogIntegral_def
#print axioms AnalyticNumberTheory.PrimeDistribution.primeCounting_partialSummation
#print axioms AnalyticNumberTheory.PrimeDistribution.primeLogIntegral_eq_main_add_tail
#print axioms AnalyticNumberTheory.PrimeDistribution.primeCounting_sub_normalizedLi_eq
#print axioms AnalyticNumberTheory.PrimeDistribution.primeCounting_normalizedLi_theta_endpoint_error
#print axioms AnalyticNumberTheory.PrimeDistribution.primeCounting_normalizedLi_integral_error
#print axioms AnalyticNumberTheory.PrimeDistribution.primeCounting_sub_normalizedLi_isBigO
