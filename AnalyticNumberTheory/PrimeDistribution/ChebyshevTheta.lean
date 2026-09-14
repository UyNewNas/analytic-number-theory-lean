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

/-- A coarser theta estimate in the form used by partial summation. -/
theorem chebyshevTheta_error :
    (Chebyshev.theta - id) =O[atTop] fun x : ℝ => x / log x := by
  obtain ⟨c, hc, hpsi⟩ := chebyshevPsi_medium_error
  have hlog : ∀ᶠ x : ℝ in atTop, log x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact (Real.log_pos hx).ne'
  have hsqrt : sqrt =o[atTop] fun x : ℝ => x / log x := by
    apply (isLittleO_mul_iff_isLittleO_div (f := log) (g := sqrt) (h := id) hlog).mp
    simpa [mul_comm] using isLittleO_sqrt_mul_log
  have hpow :
      (fun x : ℝ => (log x ^ ((1 : ℝ) / 10)) ^ (-10 : ℝ))
        =ᶠ[atTop] fun x => log x ^ (-1 : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [← Real.rpow_mul (Real.log_nonneg hx)]
    norm_num
  have hdecay :
      (fun x : ℝ => exp (-c * log x ^ ((1 : ℝ) / 10)))
        =o[atTop] fun x => log x ^ (-1 : ℝ) := by
    exact
      ((isLittleO_exp_neg_mul_rpow_atTop hc (-10)).comp_tendsto
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp tendsto_log_atTop)).congr'
        (Eventually.of_forall fun _ => rfl) hpow
  have hmedium :
      (fun x : ℝ => x * exp (-c * log x ^ ((1 : ℝ) / 10)))
        =o[atTop] fun x => x / log x := by
    simpa [Real.rpow_neg_one, div_eq_mul_inv] using
      (isBigO_refl id atTop).mul_isLittleO hdecay
  have hpsi' : (Chebyshev.psi - id) =O[atTop] fun x : ℝ => x / log x :=
    hpsi.trans hmedium.isBigO
  have hdelta : (Chebyshev.psi - Chebyshev.theta) =O[atTop]
      fun x : ℝ => x / log x :=
    Chebyshev.isBigO_psi_sub_theta_sqrt.trans hsqrt.isBigO
  calc
    Chebyshev.theta - id =
        (Chebyshev.psi - id) - (Chebyshev.psi - Chebyshev.theta) := by
      funext x
      simp only [Pi.sub_apply, id_eq]
      ring
    _ =O[atTop] fun x : ℝ => x / log x := hpsi'.sub hdelta

/-- The theta endpoint term in `primeCounting_sub_normalizedLi_eq` gains one
additional logarithm after division by `log x`.

This is the first quantitative consequence of the neutral `pi - Li`
decomposition: it uses only ANT's existing coarse theta estimate and does not
invoke the downstream Bombieri--Vinogradov application. -/
theorem primeCounting_normalizedLi_theta_endpoint_error :
    (fun x : ℝ => (log x)⁻¹ * Chebyshev.theta x - x / log x) =O[atTop]
      fun x : ℝ => x / (log x) ^ 2 := by
  have hkernel : (fun x : ℝ => (log x)⁻¹) =O[atTop] fun x : ℝ => (log x)⁻¹ :=
    isBigO_refl _ _
  have h := chebyshevTheta_error.mul hkernel
  refine h.congr' ?_ ?_
  · exact Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, id_eq, div_eq_mul_inv]
      ring
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlog : log x ≠ 0 := (Real.log_pos hx).ne'
    field_simp

/-- The partial-summation integral remainder in
`primeCounting_sub_normalizedLi_eq` is already `O(x / log^2 x)` without any
Bombieri--Vinogradov input.

The proof reuses Mathlib's two neutral integral estimates for the theta term
and for `1 / log^2`; it only transports their interval-integral form to the
`Set.Icc` form used by the stable ANT facade. This does not claim the arbitrary
fixed logarithmic saving tracked separately in issue #69. -/
theorem primeCounting_normalizedLi_integral_error :
    (fun x : ℝ =>
      (∫ t in Set.Icc 2 x, Chebyshev.theta t * (t * log t ^ 2)⁻¹) -
        ∫ t in Set.Icc 2 x, 1 / (log t) ^ 2) =O[atTop]
      fun x : ℝ => x / (log x) ^ 2 := by
  have htheta :
      (fun x : ℝ => ∫ t in Set.Icc 2 x,
        Chebyshev.theta t * (t * log t ^ 2)⁻¹) =O[atTop]
        fun x : ℝ => x / (log x) ^ 2 := by
    refine Chebyshev.integral_theta_div_log_sq_isBigO.congr' ?_
      (Eventually.of_forall fun _ => rfl)
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hx]
    apply intervalIntegral.integral_congr
    intro t _
    simp [div_eq_mul_inv]
  have hone :
      (fun x : ℝ => ∫ t in Set.Icc 2 x, 1 / (log t) ^ 2) =O[atTop]
        fun x : ℝ => x / (log x) ^ 2 := by
    refine Chebyshev.integral_one_div_log_sq_isBigO.congr' ?_
      (Eventually.of_forall fun _ => rfl)
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hx]
  exact htheta.sub hone

/-- The neutral genuine-`Li` API already gives the classical first quantitative
prime-counting remainder

`pi(x) - (2 / log 2 + primeLogIntegral x) = O(x / log^2 x)`.

This combines the exact decomposition with the endpoint and integral bounds
above. Stronger arbitrary fixed logarithmic savings require the separate
source-matched input tracked in issue #69. -/
theorem primeCounting_sub_normalizedLi_isBigO :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) -
      (2 / log 2 + primeLogIntegral x)) =O[atTop]
      fun x : ℝ => x / (log x) ^ 2 := by
  have h := primeCounting_normalizedLi_theta_endpoint_error.add
    primeCounting_normalizedLi_integral_error
  refine h.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  exact (primeCounting_sub_normalizedLi_eq x hx).symm

/-- The endpoint error in the Abel formula for reciprocal-prime sums. -/
theorem chebyshevTheta_endpoint_error :
    (fun x : ℝ => (Chebyshev.theta x - x) / (x * log x)) =O[atTop]
      fun x : ℝ => 1 / (log x) ^ 2 := by
  have hkernel : (fun x : ℝ => (x * log x)⁻¹) =O[atTop]
      fun x : ℝ => (x * log x)⁻¹ :=
    isBigO_refl _ _
  have h := chebyshevTheta_error.mul hkernel
  refine h.congr' ?_ ?_
  · exact Eventually.of_forall fun x => by simp [div_eq_mul_inv]
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : x ≠ 0 := by linarith
    have hlog : log x ≠ 0 := (Real.log_pos hx).ne'
    field_simp

end AnalyticNumberTheory.PrimeDistribution
