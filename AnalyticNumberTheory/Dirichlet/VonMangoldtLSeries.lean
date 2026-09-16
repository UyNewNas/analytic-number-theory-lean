import Mathlib.Analysis.Complex.CauchyIntegral
import AnalyticNumberTheory.Dirichlet.GRH

open scoped LSeries.notation ArithmeticFunction

namespace AnalyticNumberTheory
namespace Dirichlet

/-- On the half-plane `Re(s) > 1`, the Dirichlet-character twist of the von Mangoldt
L-series is the negative logarithmic derivative of mathlib's analytically continued
Dirichlet `LFunction`.

This is a neutral interface seam for explicit-formula arguments: it only identifies the
already-convergent twisted von-Mangoldt series with the analytic `LFunction`. It does not
supply a contour shift, a GRH error term, or a prime-character-sum estimate. -/
theorem twistedVonMangoldtLSeries_eq_negLogDerivLFunction
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    L (↗χ * ↗Λ) s =
      -deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs

/-- Under GRH, the negative logarithmic derivative of a non-principal Dirichlet
`LFunction` is analytic at every point strictly to the right of the critical line.

This is the local regularity needed before contour-integral or explicit-formula arguments;
it does not supply any quantitative bound on the logarithmic derivative. -/
theorem GRHAt.analyticAt_negLogDerivLFunction
    {N : ℕ} [NeZero N] (hGRH : GRHAt N)
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : (1 / 2 : ℝ) < s.re) :
    AnalyticAt ℂ
      (fun z : ℂ ↦
        -deriv (DirichletCharacter.LFunction χ) z /
          DirichletCharacter.LFunction χ z) s := by
  have hL : AnalyticAt ℂ (DirichletCharacter.LFunction χ) s :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
  have hD : AnalyticAt ℂ (deriv (DirichletCharacter.LFunction χ)) s := hL.deriv
  exact hD.neg.div hL (hGRH.LFunction_ne_zero_of_half_lt_re χ hχ hs)

/-- Under GRH, the negative logarithmic derivative of every fixed non-principal
Dirichlet `LFunction` is analytic throughout the open half-plane `Re(s) > 1/2`. -/
theorem GRHAt.analyticOnNhd_negLogDerivLFunction_halfPlane
    {N : ℕ} [NeZero N] (hGRH : GRHAt N)
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    AnalyticOnNhd ℂ
      (fun z : ℂ ↦
        -deriv (DirichletCharacter.LFunction χ) z /
          DirichletCharacter.LFunction χ z)
      {s : ℂ | (1 / 2 : ℝ) < s.re} := by
  intro s hs
  exact hGRH.analyticAt_negLogDerivLFunction χ hχ hs

end Dirichlet
end AnalyticNumberTheory
