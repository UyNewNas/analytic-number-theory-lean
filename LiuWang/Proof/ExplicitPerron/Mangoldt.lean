import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.PerronError.Estimate.VonMangoldtLSeries
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# An effective von Mangoldt series bound

This uses the frozen Mathlib producer `Chebyshev.psi_le_const_mul_self`,
not an unproved Rosser--Schoenfeld inequality. Its constant is `log 4 + 4`.
-/

set_option autoImplicit false

noncomputable section

open Finset MeasureTheory Filter Asymptotics
open scoped Topology

namespace LiuWang.Proof.ExplicitPerron

open BombieriVinogradov.SiegelWalfisz

theorem psi_eq_sum_one (x : ℝ) :
    Chebyshev.psi x = ∑ n ∈ Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := by
  rfl

theorem mangoldt_normSum_eq_norm (b : ℝ) :
    vonMangoldtLSeriesNormSum b =
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (b : ℂ)‖ := by
  have heq : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (b : ℂ) =
      (vonMangoldtLSeriesNormSum b : ℂ) := by
    simp only [LSeries, vonMangoldtLSeriesNormSum, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rw [norm_LSeriesTerm_vonMangoldt_eq, LSeriesTerm_vonMangoldt_eq_ofReal]
  rw [heq, Complex.norm_real, Real.norm_of_nonneg]
  exact tsum_nonneg (fun _ => norm_nonneg _)

theorem mangoldt_normSum_le {b : ℝ} (hb : 1 < b) :
    vonMangoldtLSeriesNormSum b ≤ (Real.log 4 + 4) * b / (b - 1) := by
  let C : ℝ := Real.log 4 + 4
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpsi (x : ℝ) (hx : 0 ≤ x) : Chebyshev.psi x ≤ C * x :=
    Chebyshev.psi_le_const_mul_self hx
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, ArithmeticFunction.vonMangoldt k)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    apply IsBigO.of_bound C
    filter_upwards with n
    have heq : (∑ k ∈ Icc 1 n, ArithmeticFunction.vonMangoldt k) =
        Chebyshev.psi n := by rw [psi_eq_sum_one, Nat.floor_natCast]
    simpa [Real.rpow_one, heq,
      Real.norm_of_nonneg (Chebyshev.psi_nonneg _)] using hpsi n (Nat.cast_nonneg n)
  have heq := LSeries_eq_mul_integral_of_nonneg ArithmeticFunction.vonMangoldt
    zero_le_one (s := (b : ℂ)) (by simpa using hb) hO
    (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hbound :
      ‖∫ t in Set.Ioi (1 : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt k : ℂ)) *
          (t : ℂ) ^ (-((b : ℂ) + 1))‖ ≤ C / (b - 1) := by
    have hi : IntegrableOn (fun t : ℝ => C * t ^ (-b)) (Set.Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith : -b < -1) zero_lt_one).const_mul C
    calc
      _ ≤ ∫ t in Set.Ioi (1 : ℝ), C * t ^ (-b) := by
        apply norm_integral_le_of_norm_le hi
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := zero_lt_one.trans ht
        have hs : (∑ k ∈ Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt k : ℂ)) =
            (Chebyshev.psi t : ℂ) := by
          rw [psi_eq_sum_one]
          push_cast
          rfl
        rw [hs, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (Chebyshev.psi_nonneg _),
          Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.one_re]
        calc
          Chebyshev.psi t * t ^ (-(b + 1)) ≤ C * t * t ^ (-(b + 1)) :=
            mul_le_mul_of_nonneg_right (hpsi t ht0.le) (by positivity)
          _ = C * t ^ (-b) := by
            rw [mul_assoc]
            nth_rw 1 [← Real.rpow_one t]
            rw [← Real.rpow_add ht0]
            congr 2
            ring
      _ = C / (b - 1) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -b < -1)
          zero_lt_one, Real.one_rpow]
        field_simp [show b - 1 ≠ 0 by linarith, show -b + 1 ≠ 0 by linarith]
        ring
  rw [mangoldt_normSum_eq_norm b, heq, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by linarith : 0 ≤ b)]
  calc
    _ ≤ b * (C / (b - 1)) := mul_le_mul_of_nonneg_left hbound (by linarith)
    _ = _ := by dsimp [C]; ring

end LiuWang.Proof.ExplicitPerron
