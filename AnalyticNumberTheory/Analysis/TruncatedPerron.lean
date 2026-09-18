import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.Main

/-!
# Neutral scalar truncated Perron facade

This file exposes the project-neutral scalar API consumed by downstream
analytic-number-theory work.  The implementation is the provenance-preserving
same-mathlib-pin slice vendored under `BombieriVinogradov` from
`subfish-zhou/liu-wang-ternary-goldbach-lean` at commit
`b57b7307810c37267e47110d8b5f920e3e681c81`.

No character, GRH, zero-counting, or application-specific constants enter this
facade.
-/

set_option autoImplicit false

noncomputable section

namespace AnalyticNumberTheory.Perron

/-- Perron's step weight: zero below one, half at one, and one above one. -/
abbrev stepWeight : Real -> Real :=
  BombieriVinogradov.SiegelWalfisz.perronStepWeight

/-- The scalar unsmoothed Perron integrand `y^s / s`. -/
abbrev kernelIntegrand : Real -> Complex -> Complex :=
  BombieriVinogradov.SiegelWalfisz.perronKernelIntegrand

/-- The normalized finite vertical integral of the scalar Perron kernel. -/
abbrev truncatedKernel : Real -> Real -> Real -> Complex :=
  BombieriVinogradov.SiegelWalfisz.truncatedPerronKernel

/-- Complete scalar truncated Perron estimate, including the endpoint
half-weight and the minimum of the unit and logarithmic off-endpoint errors. -/
theorem norm_truncatedKernel_sub_stepWeight_lt
    {y c T : Real} (hy : 0 < y) (hc : 0 < c) (hT : 0 < T) :
    norm (truncatedKernel y c T - (stepWeight y : Complex)) <
      if y = 1 then c / (Real.pi * T)
      else y ^ c * min 1 (1 / (Real.pi * T * abs (Real.log y))) := by
  exact BombieriVinogradov.SiegelWalfisz.norm_truncatedPerronKernel_sub_stepWeight_lt
    hy hc hT

end AnalyticNumberTheory.Perron
