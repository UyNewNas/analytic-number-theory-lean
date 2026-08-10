import AnalyticNumberTheory

/-!
# Kernel trust audit

CI checks every declaration listed below against an exact axiom whitelist:
`propext`, `Classical.choice`, and `Quot.sound`. In particular, `sorryAx` and
all other non-whitelisted axioms are rejected.
-/

#print axioms AnalyticNumberTheory.PrimeDistribution.chebyshevPsi_medium_error
#print axioms AnalyticNumberTheory.PrimeDistribution.chebyshevTheta_medium_error
#print axioms AnalyticNumberTheory.PrimeDistribution.chebyshevTheta_error
#print axioms AnalyticNumberTheory.PrimeDistribution.primeCounting_asymptotic_real
#print axioms AnalyticNumberTheory.PrimeDistribution.NatPrimeCountingPNT
#print axioms AnalyticNumberTheory.PrimeDistribution.natPrimeCountingPNT
#print axioms AnalyticNumberTheory.Mertens.log_primeProduct
#print axioms AnalyticNumberTheory.Mertens.abs_log_primeFactor_add_le
#print axioms AnalyticNumberTheory.Mertens.primeReciprocalSum_eq_theta_abel
