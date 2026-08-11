import AnalyticNumberTheory.Mertens.PartialSummation
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Finite logarithmic bridge for Mertens' product theorem

This module isolates the elementary part of the product argument.  The
identification of the limiting constant with Euler's constant is deliberately
kept separate: it requires an Euler-product/Abelian bridge, rather than only
the prime-number theorem.
-/

namespace AnalyticNumberTheory.Mertens

open Finset Real Set MeasureTheory
open Filter Topology

/-- The finite quadratic-and-higher correction in the logarithm of the prime
Euler product. -/
noncomputable def logarithmicCorrection (x : ℕ) : ℝ :=
  (primesUpTo x).sum fun p => -log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ)

/-- The correction term, extended by zero away from the primes so that it can
be treated as an ordinary series on `ℕ`. -/
noncomputable def logarithmicCorrectionTerm (p : ℕ) : ℝ :=
  if p.Prime then -log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ) else 0

/-- The candidate limiting correction constant. -/
noncomputable def logarithmicCorrectionLimit : ℝ :=
  ∑' p : ℕ, logarithmicCorrectionTerm p

/-- The filtered finite correction is the initial segment of its zero-extended
series. -/
theorem logarithmicCorrection_eq_sum_range (x : ℕ) :
    logarithmicCorrection x =
      ∑ p ∈ Finset.range (x + 1), logarithmicCorrectionTerm p := by
  unfold logarithmicCorrection primesUpTo logarithmicCorrectionTerm
  rw [Finset.sum_filter]

/-- The zero-extended logarithmic correction is absolutely summable. -/
theorem summable_logarithmicCorrectionTerm : Summable logarithmicCorrectionTerm := by
  have hsq : Summable (fun p : ℕ => 2 / (p : ℝ) ^ 2) := by
    simpa [div_eq_mul_inv] using
      ((Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num : (1 : ℕ) < 2)).mul_left 2
  refine hsq.of_norm_bounded ?_
  intro p
  unfold logarithmicCorrectionTerm
  split_ifs with hp
  · rw [Real.norm_eq_abs]
    calc
      |-log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ)| =
          |-(log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))| := by congr 1 <;> ring
      _ = |log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)| := abs_neg _
      _ ≤ 2 / (p : ℝ) ^ 2 := abs_log_primeFactor_add_le hp
  · simp only [norm_zero]
    positivity

/-- The finite correction converges to its absolutely convergent series. -/
theorem tendsto_logarithmicCorrection :
    Tendsto logarithmicCorrection atTop (𝓝 logarithmicCorrectionLimit) := by
  have hpartial : Tendsto (fun x : ℕ =>
      ∑ p ∈ Finset.range (x + 1), logarithmicCorrectionTerm p)
      atTop (𝓝 logarithmicCorrectionLimit) := by
    change Tendsto ((fun n : ℕ =>
      ∑ p ∈ Finset.range n, logarithmicCorrectionTerm p) ∘ fun x : ℕ => x + 1)
      atTop (𝓝 (∑' p : ℕ, logarithmicCorrectionTerm p))
    exact summable_logarithmicCorrectionTerm.tendsto_sum_tsum_nat.comp
      (tendsto_add_atTop_nat 1)
  have hfun : logarithmicCorrection = fun x : ℕ =>
      ∑ p ∈ Finset.range (x + 1), logarithmicCorrectionTerm p := by
    funext x
    exact logarithmicCorrection_eq_sum_range x
  rw [hfun]
  exact hpartial

/-- The difference between the limiting correction and its finite version is
the shifted tail of the absolutely convergent series. -/
theorem logarithmicCorrectionLimit_sub_eq_tail (x : ℕ) :
    logarithmicCorrectionLimit - logarithmicCorrection x =
      ∑' n : ℕ, logarithmicCorrectionTerm (n + (x + 1)) := by
  have htail := summable_logarithmicCorrectionTerm.sum_add_tsum_nat_add (x + 1)
  rw [← logarithmicCorrection_eq_sum_range] at htail
  unfold logarithmicCorrectionLimit
  linarith

/-- The correction tail is dominated by the corresponding shifted reciprocal
square series. -/
theorem logarithmicCorrection_tail_norm_le (x : ℕ) :
    ‖logarithmicCorrectionLimit - logarithmicCorrection x‖ ≤
      ∑' n : ℕ, 2 / ((n + (x + 1) : ℕ) : ℝ) ^ 2 := by
  rw [logarithmicCorrectionLimit_sub_eq_tail]
  apply tsum_of_norm_bounded
  · exact
      ((summable_nat_add_iff
        (f := fun p : ℕ => 2 / (p : ℝ) ^ 2) (x + 1)).2
        (by
          simpa [div_eq_mul_inv] using
            ((Real.summable_one_div_nat_pow (p := 2)).2
              (by norm_num : (1 : ℕ) < 2)).mul_left 2)).hasSum
  · intro n
    unfold logarithmicCorrectionTerm
    split_ifs with hp
    · rw [Real.norm_eq_abs]
      calc
        |-log (1 - 1 / ((n + (x + 1) : ℕ) : ℝ)) -
            1 / ((n + (x + 1) : ℕ) : ℝ)| =
            |-(log (1 - 1 / ((n + (x + 1) : ℕ) : ℝ)) +
              1 / ((n + (x + 1) : ℕ) : ℝ))| := by
                congr 1 <;> ring
        _ = |log (1 - 1 / ((n + (x + 1) : ℕ) : ℝ)) +
              1 / ((n + (x + 1) : ℕ) : ℝ)| := abs_neg _
        _ ≤ 2 / ((n + (x + 1) : ℕ) : ℝ) ^ 2 :=
          abs_log_primeFactor_add_le hp
    · simp only [norm_zero]
      positivity

/-- Integral comparison for the shifted reciprocal-square tail. -/
theorem shifted_reciprocal_square_tail_le (x : ℕ) (hx : 1 ≤ x) :
    ∑' n : ℕ, 2 / ((n + (x + 1) : ℕ) : ℝ) ^ 2 ≤ 2 / (x : ℝ) := by
  have hxR : 0 < (x : ℝ) := by
    exact_mod_cast (show 0 < x by omega)
  let f : ℝ → ℝ := fun t => 2 * t ^ (-2 : ℝ)
  have hanti0 : AntitoneOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ioi 0) :=
    antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)
  have hanti : AntitoneOn f (Ici (x : ℝ)) := by
    intro a ha b hb hab
    have ha0 : 0 < a := lt_of_lt_of_le hxR ha
    have hb0 : 0 < b := lt_of_lt_of_le hxR hb
    exact mul_le_mul_of_nonneg_left (hanti0 ha0 hb0 hab) (by norm_num)
  have hint : IntegrableOn f (Ioi (x : ℝ)) volume := by
    exact (integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) hxR).const_mul 2
  have hnonneg : ∀ t ∈ Ioi (x : ℝ), 0 ≤ f t := by
    intro t ht
    exact mul_nonneg (by norm_num)
      (Real.rpow_nonneg (le_of_lt (lt_trans hxR ht)) _)
  have hsum : ∑' n : ℕ, f (n + x + 1 : ℕ) ≤ ∫ t in Ioi (x : ℝ), f t :=
    hanti.tsum_comp_add_le_integral x hint hnonneg
  calc
    ∑' n : ℕ, 2 / ((n + (x + 1) : ℕ) : ℝ) ^ 2 =
        ∑' n : ℕ, f (n + x + 1 : ℕ) := by
          apply tsum_congr
          intro n
          dsimp [f]
          have hp : 0 < ((n + x + 1 : ℕ) : ℝ) := by positivity
          have hcast : ((n + (x + 1) : ℕ) : ℝ) = (n + x + 1 : ℕ) := by
            push_cast
            ring
          rw [hcast, Real.rpow_neg (le_of_lt hp)]
          norm_num
          ring
    _ ≤ ∫ t in Ioi (x : ℝ), f t := hsum
    _ = 2 / (x : ℝ) := by
      dsimp [f]
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hxR]
      rw [show (-2 : ℝ) + 1 = -1 by norm_num,
        Real.rpow_neg (le_of_lt hxR)]
      field_simp
      simp

/-- Explicit `O(1/x)` bound for the logarithmic correction tail. -/
theorem logarithmicCorrection_tail_norm_le_div (x : ℕ) (hx : 1 ≤ x) :
    ‖logarithmicCorrectionLimit - logarithmicCorrection x‖ ≤ 2 / (x : ℝ) :=
  (logarithmicCorrection_tail_norm_le x).trans
    (shifted_reciprocal_square_tail_le x hx)

/-- On the Mertens scale, the logarithmic correction tail is negligible. -/
theorem logarithmicCorrection_tail_isBigO :
    (fun n : ℕ => logarithmicCorrectionLimit - logarithmicCorrection n) =O[atTop]
      fun n => 1 / log (n : ℝ) := by
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : 0 < (n : ℝ) := by positivity
  have hlog0 : 0 < log (n : ℝ) := Real.log_pos hn1
  have hlog_le : log (n : ℝ) ≤ n := by
    have h := Real.log_le_sub_one_of_pos hn0
    linarith
  have hinv : 1 / (n : ℝ) ≤ 1 / log (n : ℝ) :=
    one_div_le_one_div_of_le hlog0 hlog_le
  calc
    ‖logarithmicCorrectionLimit - logarithmicCorrection n‖ ≤ 2 / (n : ℝ) :=
      logarithmicCorrection_tail_norm_le_div n (by omega)
    _ ≤ 2 * ‖1 / log (n : ℝ)‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hlog0)]
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)

/-- Taking the logarithm of the finite Euler product separates the reciprocal
prime sum from its convergent higher-order correction. -/
theorem neg_log_primeProduct_eq_reciprocal_add_correction (x : ℕ) :
    -log (primeProduct x) = primeReciprocalSum x + logarithmicCorrection x := by
  rw [log_primeProduct]
  unfold primeReciprocalSum logarithmicCorrection
  rw [← Finset.sum_neg_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- The logarithmic product error is the sum of the Mertens-II error and the
convergent higher-order correction tail. -/
theorem log_primeProduct_error_eq (n : ℕ) :
    log (primeProduct n) + log (log (n : ℝ)) +
        (mertensSecondConstant + logarithmicCorrectionLimit) =
      -(primeReciprocalSum n -
          (log (log (n : ℝ)) + mertensSecondConstant)) +
        (logarithmicCorrectionLimit - logarithmicCorrection n) := by
  have h := neg_log_primeProduct_eq_reciprocal_add_correction n
  linarith

/-- Mertens' product logarithm with its canonical (not yet identified as
Euler--Mascheroni) constant. -/
theorem log_primeProduct_mertens_isBigO :
    (fun n : ℕ => log (primeProduct n) + log (log (n : ℝ)) +
      (mertensSecondConstant + logarithmicCorrectionLimit)) =O[atTop]
      fun n => 1 / log (n : ℝ) := by
  refine (mertensSecond_isBigO.neg_left.add logarithmicCorrection_tail_isBigO).congr_left ?_
  intro n
  exact (log_primeProduct_error_eq n).symm

end AnalyticNumberTheory.Mertens
