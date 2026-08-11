import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Zeta--von Mangoldt bridge for Mertens constants

This module begins the constant-identification workline.  It records the
analytic normalization at `s = 1`; connecting it to hard prime cutoffs is the
remaining Abelian bridge.
-/

namespace AnalyticNumberTheory.Mertens

open Filter Topology Asymptotics

/-- The logarithm of zeta, expressed through the von Mangoldt Dirichlet
series, has the standard normalized `O(s - 1)` behavior at `1` from the
right. -/
theorem zeta_log_vonMangoldt_isBigO :
    (fun s : ℝ =>
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
        ((n : ℝ) ^ s * Real.log n)) + Real.log (s - 1)) =O[𝓝[>] 1]
      fun s => s - 1 := by
  refine log_riemannZeta_add_log_sub_isBigO_ofReal.congr' ?_ .rfl
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  rw [log_riemannZeta_eq hs]

/-- The prime Euler-log expansion of the zeta logarithm.  This is the
analytic prime-side counterpart of the finite product bridge. -/
theorem zeta_euler_log_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    ∑' p : Nat.Primes, -Complex.log
      (1 - (1 : DirichletCharacter ℂ 1) p * (p : ℂ) ^ (-s)) =
      LSeries
        (fun n : ℕ => (1 : DirichletCharacter ℂ 1) n *
          ArithmeticFunction.vonMangoldt n / Real.log n) s :=
  DirichletCharacter.eulerProduct_log_eq_LSeries
    (χ := (1 : DirichletCharacter ℂ 1)) hs

end AnalyticNumberTheory.Mertens
