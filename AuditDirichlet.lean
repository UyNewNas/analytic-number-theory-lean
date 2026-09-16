import AnalyticNumberTheory.Dirichlet.GRH
import AnalyticNumberTheory.Dirichlet.Orthogonality

/-!
# Reusable Dirichlet core trust audit

This focused audit accompanies the extracted downstream-neutral GRH and character
orthogonality API. CI enforces the same axiom whitelist as the repository-wide audit.
The four LargeSieve declarations are direct dependencies reused by the new facade/kernel layer.
-/

#print axioms AnalyticNumberTheory.Dirichlet.GRH.at
#print axioms AnalyticNumberTheory.Dirichlet.grhAt_iff
#print axioms AnalyticNumberTheory.Dirichlet.GRHAt.zeroFreeRectangle
#print axioms AnalyticNumberTheory.LargeSieve.charOrthSum
#print axioms AnalyticNumberTheory.LargeSieve.charOrthSum_unit
#print axioms AnalyticNumberTheory.LargeSieve.charIndicator_zmod
#print axioms AnalyticNumberTheory.LargeSieve.charIndicator
#print axioms AnalyticNumberTheory.Dirichlet.charOrthSumUnit
#print axioms AnalyticNumberTheory.Dirichlet.charOrthMulKernel
#print axioms AnalyticNumberTheory.Dirichlet.charOrthMulKernel_prime
#print axioms AnalyticNumberTheory.Dirichlet.charOrthKernel_prime_two
