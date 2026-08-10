import AnalyticNumberTheory.PrimeDistribution.PrimeNumberTheorem
import Mathlib.NumberTheory.Chebyshev

/-!
# Effective Chebyshev theta estimate

This is the quantitative bridge from the PNTAnd estimate for `psi` to the
prime-only Chebyshev function `theta`. It is the analytic input used by the
Mertens partial-summation development.
-/

namespace AnalyticNumberTheory.PrimeDistribution

open Asymptotics Filter Real
open scoped Chebyshev

/-- The medium PNT error for `psi` transfers to `theta`, with the standard
`sqrt x` prime-power correction retained explicitly. -/
theorem chebyshevTheta_medium_error :
    ∃ c > 0,
      (Chebyshev.theta - id) =O[atTop]
        fun x : ℝ => sqrt x + x * exp (-c * log x ^ ((1 : ℝ) / 10)) := by
  obtain ⟨c, hc, hpsi⟩ := chebyshevPsi_medium_error
  refine ⟨c, hc, ?_⟩
  have htheta_psi : (Chebyshev.theta - Chebyshev.psi) =O[atTop] sqrt := by
    rw [show Chebyshev.theta - Chebyshev.psi =
      fun x => -((Chebyshev.psi - Chebyshev.theta) x) by
        funext x
        simp only [Pi.sub_apply, neg_sub]]
    exact Chebyshev.isBigO_psi_sub_theta_sqrt.neg_left
  have hsqrt : sqrt =O[atTop]
      fun x : ℝ => sqrt x + x * exp (-c * log x ^ ((1 : ℝ) / 10)) :=
    IsBigO.of_bound' <| eventually_atTop.2 ⟨1, fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg _), Real.norm_eq_abs,
        abs_of_nonneg]
      · exact le_add_of_nonneg_right (mul_nonneg (by linarith) (le_of_lt (exp_pos _)))
      · exact add_nonneg (sqrt_nonneg _) (mul_nonneg (by linarith) (le_of_lt (exp_pos _)))⟩
  have hpsi_bound : (fun x : ℝ => x * exp (-c * log x ^ ((1 : ℝ) / 10))) =O[atTop]
      fun x : ℝ => sqrt x + x * exp (-c * log x ^ ((1 : ℝ) / 10)) :=
    IsBigO.of_bound' <| eventually_atTop.2 ⟨1, fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) (le_of_lt (exp_pos _))),
        Real.norm_eq_abs, abs_of_nonneg]
      · exact le_add_of_nonneg_left (sqrt_nonneg _)
      · exact add_nonneg (sqrt_nonneg _) (mul_nonneg (by linarith) (le_of_lt (exp_pos _)))⟩
  have hpsi' : (fun x : ℝ => Chebyshev.psi x - x) =O[atTop]
      fun x : ℝ => sqrt x + x * exp (-c * log x ^ ((1 : ℝ) / 10)) := by
    change (fun x : ℝ => Chebyshev.psi x - x) =O[atTop]
      (fun x : ℝ => x * exp (-c * log x ^ ((1 : ℝ) / 10))) at hpsi
    exact hpsi.trans hpsi_bound
  calc
    Chebyshev.theta - id =
        fun x => Chebyshev.theta x - Chebyshev.psi x + (Chebyshev.psi x - x) := by
      funext x
      simp only [Pi.sub_apply, id_eq]
      ring
    _ =O[atTop] fun x : ℝ => sqrt x + x * exp (-c * log x ^ ((1 : ℝ) / 10)) :=
      (htheta_psi.trans hsqrt).add hpsi'

end AnalyticNumberTheory.PrimeDistribution
