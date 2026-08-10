import AnalyticNumberTheory

/-!
# Kernel trust audit

These are all declarations in the stable public API. CI rejects the audit if
any declaration depends on `sorryAx`. The foundational axioms normally used by
mathlib (`propext`, `Classical.choice`, and `Quot.sound`) are permitted.
-/

#print axioms AnalyticNumberTheory.PrimeDistribution.chebyshevPsi_medium_error
#print axioms AnalyticNumberTheory.PrimeDistribution.primeCounting_asymptotic_real
#print axioms AnalyticNumberTheory.PrimeDistribution.NatPrimeCountingPNT
#print axioms AnalyticNumberTheory.PrimeDistribution.natPrimeCountingPNT
#print axioms AnalyticNumberTheory.Mertens.log_primeProduct
#print axioms AnalyticNumberTheory.Mertens.abs_log_primeFactor_add_le
