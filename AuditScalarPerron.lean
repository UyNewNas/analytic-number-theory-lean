import AnalyticNumberTheory.Analysis.TruncatedPerron

/-!
# Scalar Perron trust audit

The focused surface is deliberately small: three neutral data definitions and
the complete all-cases truncated Perron bound.  CI enforces the same exact
axiom whitelist as the rest of ANT.
-/

#print axioms AnalyticNumberTheory.Perron.stepWeight
#print axioms AnalyticNumberTheory.Perron.kernelIntegrand
#print axioms AnalyticNumberTheory.Perron.truncatedKernel
#print axioms AnalyticNumberTheory.Perron.norm_truncatedKernel_sub_stepWeight_lt
