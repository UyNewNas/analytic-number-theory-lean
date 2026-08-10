import AnalyticNumberTheory.Mertens.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev

/-!
# Abel summation for prime reciprocal sums

This finite identity is the bridge from effective Chebyshev-theta estimates to
Mertens' second theorem.  It deliberately contains no asymptotic claim.
-/

namespace AnalyticNumberTheory.Mertens

open Finset MeasureTheory Real
open scoped Chebyshev

private theorem deriv_inv_mul_log {x : ℝ} (hx : 2 ≤ x) :
    deriv (fun u : ℝ => (u * log u)⁻¹) x =
      -(log x + 1) / (x * log x) ^ 2 := by
  have hx0 : x ≠ 0 := by linarith
  have hxlog : log x ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  change deriv (id * log)⁻¹ x = _
  convert ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)).inv
    (mul_ne_zero hx0 hxlog) |>.deriv using 1
  simp only [Pi.mul_apply, id_eq, one_mul]
  field_simp [hx0, hxlog]

/-- Abel summation expresses the finite reciprocal-prime sum through the
Chebyshev theta function. -/
theorem primeReciprocalSum_eq_theta_abel {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocalSum ⌊x⌋₊ =
      (x * log x)⁻¹ * Chebyshev.theta x -
        ∫ t in 2..x,
          deriv (fun u : ℝ => (u * log u)⁻¹) t * Chebyshev.theta t := by
  let a : ℕ → ℝ := Set.indicator (Set.ofPred Nat.Prime) fun n ↦ log n
  unfold primeReciprocalSum primesUpTo
  rw [Nat.range_succ_eq_Icc_zero, sum_filter]
  trans ∑ n ∈ Icc 0 ⌊x⌋₊, (n * log n)⁻¹ * a n
  · refine sum_congr rfl fun n hn ↦ ?_
    split_ifs with hp
    · have hlog : log (n : ℝ) ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one
          (by exact_mod_cast hp.pos) (by exact_mod_cast hp.ne_one)
      simp [a, hp]
      field_simp
    · simp [a, hp]
  rw [sum_mul_eq_sub_integral_mul₁ a (f := fun u : ℝ => (u * log u)⁻¹)
    (by simp [a]) (by simp [a]) x]
  · rw [← intervalIntegral.integral_of_le hx]
    simp only [a, Set.indicator_apply, sum_filter, Chebyshev.theta_eq_sum_Icc]
    grind
  · intro z hz
    have hz0 : z ≠ 0 := by linarith [hz.1]
    have hzlog : log z ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [hz.1]) (by linarith [hz.1])
    exact ((hasDerivAt_id z).mul (Real.hasDerivAt_log hz0)).inv (mul_ne_zero hz0 hzlog) |>.differentiableAt
  · refine ContinuousOn.integrableOn_Icc fun z hz ↦ ?_
    have hcont : ContinuousOn (fun y : ℝ => -(log y + 1) / (y * log y) ^ 2) (Set.Icc 2 x) := by
      have hlogcont : ContinuousOn log (Set.Icc 2 x) := fun y hy ↦
        (Real.continuousAt_log (by linarith [hy.1])).continuousWithinAt
      refine (hlogcont.add continuousOn_const).neg.div
        (((continuousOn_id' (Set.Icc 2 x)).mul hlogcont).pow 2) fun y hy ↦ ?_
      exact pow_ne_zero 2 <| mul_ne_zero (by linarith [hy.1])
        (Real.log_ne_zero_of_pos_of_ne_one (by linarith [hy.1]) (by linarith [hy.1]))
    exact (ContinuousOn.congr hcont fun y hy ↦ deriv_inv_mul_log hy.1) z hz

/-- The positive-kernel form of the Abel bridge. -/
theorem primeReciprocalSum_eq_theta_div_mul_log_add_integral {x : ℝ} (hx : 2 ≤ x) :
    primeReciprocalSum ⌊x⌋₊ =
      Chebyshev.theta x / (x * log x) +
        ∫ t in 2..x, Chebyshev.theta t * (log t + 1) / (t * log t) ^ 2 := by
  rw [primeReciprocalSum_eq_theta_abel hx]
  rw [show (x * log x)⁻¹ * Chebyshev.theta x = Chebyshev.theta x / (x * log x) by ring,
    sub_eq_add_neg, ← intervalIntegral.integral_neg]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht2 : 2 ≤ t := by
    rcases Set.mem_uIcc.mp ht with h | h
    · exact h.1
    · linarith [h.2]
  change -(deriv (fun u : ℝ => (u * log u)⁻¹) t * Chebyshev.theta t) = _
  rw [deriv_inv_mul_log ht2]
  ring

end AnalyticNumberTheory.Mertens
