import AnalyticNumberTheory.Dirichlet.CompletedReflection
import AnalyticNumberTheory.Dirichlet.GammaFactorRegularity
import Mathlib.Analysis.Analytic.Order

/-!
# Zero multiplicity for the symmetric completed Dirichlet L-function

Project-neutral extraction/adaptation of
`subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`,
`BombieriVinogradov/Proof/SiegelWalfisz/ZeroFree/CompletedLFunctionOrder.lean`.

In the positive half-plane, the symmetric normalization and gamma factor are analytic and
nonvanishing. Therefore completion preserves the analytic zero multiplicity of the ordinary
Dirichlet L-function. No zero index, zero-counting hierarchy, GRH, contour, or application-specific
parameter is imported here.
-/

set_option autoImplicit false

namespace AnalyticNumberTheory.Dirichlet

/-- In `Re(s) > 0`, the symmetric completed Dirichlet L-function has exactly the same analytic
zero multiplicity as the ordinary Dirichlet L-function. -/
theorem analyticOrderNatAt_symmetricCompletedLFunction_eq_LFunction
    {N : Nat} [NeZero N] {χ : DirichletCharacter Complex N}
    (hχ : χ ≠ 1) {s : Complex} (hs : 0 < s.re) :
    analyticOrderNatAt (symmetricCompletedLFunction χ) s =
      analyticOrderNatAt χ.LFunction s := by
  have hHalfPlane : {z : Complex | 0 < z.re} ∈ nhds s :=
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs
  have hEventually :
      symmetricCompletedLFunction χ =ᶠ[nhds s]
        fun z : Complex =>
          (N : Complex) ^ (z / 2) *
            (χ.LFunction z * χ.gammaFactor z) := by
    filter_upwards [hHalfPlane] with z hz
    rw [symmetricCompletedLFunction,
      DirichletCharacter.completedLFunction_eq_LFunction_mul_gammaFactor_of_re_pos χ hz]
  have hN : (N : Complex) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  have hNormalizationAnalytic :
      AnalyticAt Complex (fun z : Complex => (N : Complex) ^ (z / 2)) s :=
    ((differentiable_id.div_const (2 : Complex)).const_cpow (.inl hN)).analyticAt s
  have hLFunctionAnalytic : AnalyticAt Complex χ.LFunction s :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
  have hGammaAnalytic : AnalyticAt Complex χ.gammaFactor s := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hHalfPlane] with z hz
    exact differentiableAt_gammaFactor_of_re_pos χ hz
  have hNormalizationNe : (N : Complex) ^ (s / 2) ≠ 0 := by
    simp [hN]
  have hGammaNe : χ.gammaFactor s ≠ 0 :=
    gammaFactor_ne_zero_of_re_pos χ hs
  have hNormalizationOrder :
      analyticOrderAt (fun z : Complex => (N : Complex) ^ (z / 2)) s = 0 :=
    hNormalizationAnalytic.analyticOrderAt_eq_zero.mpr hNormalizationNe
  have hGammaOrder : analyticOrderAt χ.gammaFactor s = 0 :=
    hGammaAnalytic.analyticOrderAt_eq_zero.mpr hGammaNe
  have hProductOrder :
      analyticOrderAt
          (fun z : Complex =>
            (N : Complex) ^ (z / 2) *
              (χ.LFunction z * χ.gammaFactor z)) s =
        analyticOrderAt χ.LFunction s := by
    change analyticOrderAt
        ((fun z : Complex => (N : Complex) ^ (z / 2)) *
          (χ.LFunction * χ.gammaFactor)) s = _
    rw [analyticOrderAt_mul hNormalizationAnalytic
      (hLFunctionAnalytic.mul hGammaAnalytic)]
    rw [analyticOrderAt_mul hLFunctionAnalytic hGammaAnalytic]
    rw [hNormalizationOrder, hGammaOrder, zero_add, add_zero]
  have hProductOrderNat :
      analyticOrderNatAt
          (fun z : Complex =>
            (N : Complex) ^ (z / 2) *
              (χ.LFunction z * χ.gammaFactor z)) s =
        analyticOrderNatAt χ.LFunction s := by
    simpa [analyticOrderNatAt] using congrArg ENat.toNat hProductOrder
  have hCompletedOrderNat :
      analyticOrderNatAt (symmetricCompletedLFunction χ) s =
        analyticOrderNatAt
          (fun z : Complex =>
            (N : Complex) ^ (z / 2) *
              (χ.LFunction z * χ.gammaFactor z)) s := by
    simpa [analyticOrderNatAt] using
      congrArg ENat.toNat (analyticOrderAt_congr hEventually)
  exact hCompletedOrderNat.trans hProductOrderNat

end AnalyticNumberTheory.Dirichlet
