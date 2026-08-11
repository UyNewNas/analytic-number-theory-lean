import AnalyticNumberTheory.Mertens.Basic
import AnalyticNumberTheory.PrimeDistribution.ChebyshevTheta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev

/-!
# Abel summation for prime reciprocal sums

This finite identity is the bridge from effective Chebyshev-theta estimates to
Mertens' second theorem.  It deliberately contains no asymptotic claim.
-/

namespace AnalyticNumberTheory.Mertens

open Asymptotics Filter Finset MeasureTheory Real
open scoped Chebyshev

/-- The theta-error contribution to the positive-kernel Abel formula. -/
noncomputable def thetaErrorKernel (t : ℝ) : ℝ :=
  (Chebyshev.theta t - t) * (log t + 1) / (t * log t) ^ 2

theorem thetaErrorKernel_eq (t : ℝ) :
    thetaErrorKernel t =
      Chebyshev.theta t * (log t + 1) / (t * log t) ^ 2 -
        t * (log t + 1) / (t * log t) ^ 2 := by
  unfold thetaErrorKernel
  ring

/-- A reusable improper-integral tail estimate for the kernel that occurs in
the Mertens error term. -/
theorem norm_integral_Ioi_le_div_log {f : ℝ → ℝ} {x C : ℝ} (hx : 1 < x)
    (hbound : ∀ t ∈ Set.Ioi x, ‖f t‖ ≤ C * (t⁻¹ / (log t) ^ 2)) :
    ‖∫ t in Set.Ioi x, f t‖ ≤ C / log x := by
  have hk : IntegrableOn (fun t : ℝ => t⁻¹ / (log t) ^ 2) (Set.Ioi x) volume :=
    integrableOn_inv_div_log_sq_Ioi hx
  have hCk : IntegrableOn (fun t : ℝ => C * (t⁻¹ / (log t) ^ 2)) (Set.Ioi x) volume :=
    hk.const_mul C
  calc
    ‖∫ t in Set.Ioi x, f t‖ ≤ ∫ t in Set.Ioi x, C * (t⁻¹ / (log t) ^ 2) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hCk
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hbound t ht
    _ = C * ∫ t in Set.Ioi x, t⁻¹ / (log t) ^ 2 := by rw [integral_const_mul]
    _ = C / log x := by rw [integral_inv_div_log_sq_Ioi hx]; ring

/-- The Chebyshev theta function is locally integrable away from zero. -/
theorem locallyIntegrableOn_theta :
    LocallyIntegrableOn Chebyshev.theta (Set.Ici (2 : ℝ)) volume := by
  let c : ℕ → ℝ := fun p => if p.Prime then log p else 0
  have h : LocallyIntegrableOn
      (fun t : ℝ => (1 : ℝ) * ∑ p ∈ Icc 0 ⌊t⌋₊, c p) (Set.Ici 2) volume := by
    exact locallyIntegrableOn_mul_sum_Icc c (by norm_num) (locallyIntegrableOn_const 1)
  have htheta : Chebyshev.theta = fun t : ℝ => ∑ p ∈ Icc 0 ⌊t⌋₊, c p := by
    ext t
    rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rw [htheta]
  simpa using h

/-- The theta-error kernel is locally integrable away from the logarithmic
singularity. -/
theorem locallyIntegrableOn_thetaErrorKernel :
    LocallyIntegrableOn thetaErrorKernel (Set.Ici 2) volume := by
  have herror : LocallyIntegrableOn (fun t : ℝ => Chebyshev.theta t - t)
      (Set.Ici 2) volume :=
    locallyIntegrableOn_theta.sub
      (ContinuousOn.locallyIntegrableOn (by fun_prop) measurableSet_Ici)
  have hcont : ContinuousOn (fun t : ℝ => (log t + 1) / (t * log t) ^ 2) (Set.Ici 2) := by
    have hlog : ContinuousOn log (Set.Ici 2) := fun t ht => by
      change 2 ≤ t at ht
      exact (Real.continuousAt_log (by linarith)).continuousWithinAt
    refine (hlog.add continuousOn_const).div
      (((continuousOn_id' _).mul hlog).pow 2) fun t ht => ?_
    change 2 ≤ t at ht
    exact pow_ne_zero 2 <| mul_ne_zero (by linarith)
      (Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith))
  unfold thetaErrorKernel
  simpa [mul_div_assoc, mul_comm, mul_left_comm] using
    herror.continuousOn_mul hcont isLocallyClosed_Ici

/-- The theta-error kernel has the integrable decay required for the Mertens
tail estimate. -/
theorem thetaErrorKernel_isBigO :
    thetaErrorKernel =O[atTop] fun t : ℝ => t⁻¹ / (log t) ^ 2 := by
  obtain ⟨K, hK, htheta⟩ := Asymptotics.isBigO_iff'.mp
    AnalyticNumberTheory.PrimeDistribution.chebyshevTheta_error
  refine Asymptotics.isBigO_iff'.mpr ⟨2 * K, mul_pos (by norm_num) hK, ?_⟩
  filter_upwards [htheta, eventually_ge_atTop (exp 1)] with t hE ht
  have ht0 : 0 < t := lt_of_lt_of_le (exp_pos 1) ht
  have hlog1 : 1 ≤ log t := (Real.le_log_iff_exp_le ht0).mpr ht
  have hlog0 : 0 < log t := lt_of_lt_of_le zero_lt_one hlog1
  have hplus : log t + 1 ≤ 2 * log t := by linarith
  have hEabs : |Chebyshev.theta t - t| ≤ K * (t / log t) := by
    simpa only [Pi.sub_apply, id_eq, Real.norm_eq_abs,
      abs_of_pos (div_pos ht0 hlog0)] using hE
  have hfactor : (log t + 1) / (t * log t) ^ 2 ≤ 2 / (t ^ 2 * log t) := by
    field_simp [ne_of_gt ht0, ne_of_gt hlog0]
    linarith [hplus]
  have hfactor0 : 0 ≤ (log t + 1) / (t * log t) ^ 2 := by positivity
  rw [show ‖thetaErrorKernel t‖ = |Chebyshev.theta t - t| *
      ((log t + 1) / (t * log t) ^ 2) by
        unfold thetaErrorKernel
        calc
          |(Chebyshev.theta t - t) * (log t + 1) / (t * log t) ^ 2| =
              |Chebyshev.theta t - t| * |log t + 1| / |(t * log t) ^ 2| := by
                rw [abs_div, abs_mul]
          _ = |Chebyshev.theta t - t| * ((log t + 1) / (t * log t) ^ 2) := by
                rw [abs_of_nonneg (by linarith : 0 ≤ log t + 1),
                  abs_of_nonneg (sq_nonneg (t * log t))]
                ring]
  calc
    |Chebyshev.theta t - t| * ((log t + 1) / (t * log t) ^ 2) ≤
        (K * (t / log t)) * ((log t + 1) / (t * log t) ^ 2) :=
      mul_le_mul_of_nonneg_right hEabs hfactor0
    _ ≤ (K * (t / log t)) * (2 / (t ^ 2 * log t)) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = (2 * K) * ‖t⁻¹ / (log t) ^ 2‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < t⁻¹ / (log t) ^ 2)]
      have htne : t ≠ 0 := ne_of_gt ht0
      have hlogne : log t ≠ 0 := ne_of_gt hlog0
      field_simp [htne, hlogne]

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

/-- The contribution of replacing `theta` by the identity in the positive-kernel
Abel formula. -/
theorem theta_abel_main_term {x : ℝ} (hx : 2 ≤ x) :
    x / (x * log x) +
        ∫ t in 2..x, t * (log t + 1) / (t * log t) ^ 2 =
      log (log x) + (-log (log 2) + 1 / log 2) := by
  have hx1 : 1 < x := by linarith
  have hkernel :
      (∫ t in 2..x, t * (log t + 1) / (t * log t) ^ 2) =
        ∫ t in 2..x, (t⁻¹ / log t + t⁻¹ / log t ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht2 : 2 ≤ t := by
      rcases Set.mem_uIcc.mp ht with h | h
      · exact h.1
      · linarith [h.2]
    have ht0 : t ≠ 0 := by linarith
    have htlog : log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one
      (by linarith) (by linarith)
    field_simp
  have hfirst : IntervalIntegrable (fun t : ℝ => t⁻¹ / log t) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    fun_prop (disch := grind [Real.log_pos, Set.uIcc])
  have hsecond : IntervalIntegrable (fun t : ℝ => t⁻¹ / log t ^ 2) volume 2 x := by
    have hlog : ContinuousOn log (Set.uIcc (2 : ℝ) x) := fun t ht ↦
      (Real.continuousAt_log (by
        rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1, h.2])).continuousWithinAt
    have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc 2 x) :=
      (continuousOn_id' _).inv₀ fun t ht ↦ by
        rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1, h.2]
    apply ContinuousOn.intervalIntegrable
    exact hinv.div (hlog.pow 2) fun t ht ↦ pow_ne_zero 2 <|
      Real.log_ne_zero_of_pos_of_ne_one
        (by rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1, h.2])
        (by rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1, h.2])
  rw [hkernel, intervalIntegral.integral_add hfirst hsecond,
    integral_inv_div_log (by norm_num) hx1, integral_inv_div_log_sq (by norm_num) hx1]
  field_simp
  ring

end AnalyticNumberTheory.Mertens
