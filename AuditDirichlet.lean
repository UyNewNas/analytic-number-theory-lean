import AnalyticNumberTheory.Dirichlet.GRH
import AnalyticNumberTheory.Dirichlet.Orthogonality
import AnalyticNumberTheory.Dirichlet.Decomposition

/-!
# Reusable Dirichlet core trust audit

This focused audit covers every public theorem added by the extracted downstream-neutral
GRH, character-orthogonality, and principal/nonprincipal decomposition layers. CI enforces
the same exact axiom whitelist as the repository-wide audit.
-/

#print axioms AnalyticNumberTheory.Dirichlet.GRH.at
#print axioms AnalyticNumberTheory.Dirichlet.grhAt_iff
#print axioms AnalyticNumberTheory.Dirichlet.GRHAt.zeroFreeRectangle
#print axioms AnalyticNumberTheory.Dirichlet.charOrthSumUnit
#print axioms AnalyticNumberTheory.Dirichlet.charOrthMulKernel
#print axioms AnalyticNumberTheory.Dirichlet.charOrthMulKernel_prime
#print axioms AnalyticNumberTheory.Dirichlet.charOrthKernel_prime_two
#print axioms AnalyticNumberTheory.Dirichlet.mem_nonprincipalCharacters
#print axioms AnalyticNumberTheory.Dirichlet.sum_chars_eq_principal_add_nonprincipal
#print axioms AnalyticNumberTheory.Dirichlet.charOrthMulKernel_prime_nonprincipal
#print axioms AnalyticNumberTheory.Dirichlet.weightedCharKernelCollapse_prime
#print axioms AnalyticNumberTheory.Dirichlet.weightedPrincipalKernel_prime
#print axioms AnalyticNumberTheory.Dirichlet.weightedNonprincipalKernelCollapse_prime
