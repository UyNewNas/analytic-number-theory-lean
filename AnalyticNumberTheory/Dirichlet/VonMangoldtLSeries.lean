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

end Dirichlet
end AnalyticNumberTheory
