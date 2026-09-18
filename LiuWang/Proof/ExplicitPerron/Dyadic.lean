import LiuWang.Proof.ExplicitPerron.Series
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Explicit dyadic finite Perron majorant

The tail uses the convergent norm series; the central range is a finite,
explicit sum, with no unnamed constant or analytic premise.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace LiuWang.Proof.ExplicitPerron

def central (x : ℝ) : Finset ℕ :=
  (Icc 1 ⌊2 * x⌋₊).filter (fun n => x / 2 < (n : ℝ))

def centralCost (a : ℕ → ℂ) (x b : ℝ) : ℝ :=
  ∑ n ∈ central x, ‖a n‖ * (x / n) ^ b / |Real.log (x / n)|

theorem log_two_le_abs_log_far {x : ℝ} {n : ℕ} (hx : 0 < x)
    (hn : n ≠ 0) (hfar : n ∉ central x) :
    Real.log 2 ≤ |Real.log (x / n)| := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hr : 0 < x / n := div_pos hx hn0
  by_cases hlo : (n : ℝ) ≤ x / 2
  · have hratio : (2 : ℝ) ≤ x / n := (le_div_iff₀ hn0).2 (by linarith)
    exact (Real.log_le_log (by norm_num) hratio).trans (le_abs_self _)
  · have hhi : 2 * x < (n : ℝ) := by
      by_contra h
      apply hfar
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn,
        (Nat.le_floor_iff (by positivity)).2 (le_of_not_gt h)⟩, lt_of_not_ge hlo⟩
    have hratio : x / n ≤ (1 / 2 : ℝ) :=
      (div_le_iff₀ hn0).2 (by linarith)
    have hlog := Real.log_le_log hr hratio
    rw [show Real.log (1 / 2 : ℝ) = -Real.log 2 by rw [one_div, Real.log_inv]] at hlog
    exact (by linarith : Real.log 2 ≤ -Real.log (x / n)).trans (neg_le_abs _)

theorem majorant_le_dyadic (a : ℕ → ℂ) {x b T : ℝ}
    (hx : 0 < x) (hxn : ∀ n : ℕ, x ≠ n) (hb : 0 < b) (hT : 0 < T)
    (n : ℕ) :
    majorant a x b T n ≤
      x ^ b / (Real.pi * T * Real.log 2) * ‖LSeries.term a (b : ℂ) n‖ +
      (if n ∈ central x then
        (‖a n‖ * (x / n) ^ b / |Real.log (x / n)|) / (Real.pi * T)
        else 0) := by
  by_cases hn : n = 0
  · simp [majorant, LSeries.term_def, central, hn]
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hbase : 0 ≤ x ^ b / (Real.pi * T * Real.log 2) *
      ‖LSeries.term a (b : ℂ) n‖ := by positivity
  have hbound : majorant a x b T n ≤
      (‖a n‖ * (x / n) ^ b / |Real.log (x / n)|) / (Real.pi * T) := by
    simp only [majorant, hn, if_false, ratio_ne_one hxn hn]
    calc
      _ ≤ ‖a n‖ * ((x / n) ^ b * (1 / (Real.pi * T * |Real.log (x / n)|))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)) (norm_nonneg _)
      _ = _ := by ring
  by_cases hnear : n ∈ central x
  · rw [if_pos hnear]
    exact hbound.trans (le_add_of_nonneg_left hbase)
  · rw [if_neg hnear, add_zero]
    apply hbound.trans
    rw [LSeries.term_def, if_neg hn, norm_div,
      Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa using hb.ne')]
    simp only [Complex.ofReal_re]
    rw [Real.div_rpow hx.le hn0.le]
    calc
      _ ≤ (‖a n‖ * (x ^ b / (n : ℝ) ^ b) / Real.log 2) / (Real.pi * T) := by
        gcongr
        exact log_two_le_abs_log_far hx hn hnear
      _ = _ := by ring

theorem norm_vertical_sub_sum_le_dyadic (a : ℕ → ℂ) {x b T : ℝ}
    (hx : 0 < x) (hxn : ∀ n : ℕ, x ≠ n) (hb : 0 < b) (hT : 0 < T)
    (ha : LSeriesSummable a (b : ℂ)) :
    ‖vertical (seriesIntegrand a x) b (-T) T -
      ∑ n ∈ Icc 1 ⌊x⌋₊, a n‖ ≤
      (x ^ b / Real.log 2 * ∑' n, ‖LSeries.term a (b : ℂ) n‖ +
        centralCost a x b) / (Real.pi * T) := by
  have hfin : Summable (fun n => if n ∈ central x then
      (‖a n‖ * (x / n) ^ b / |Real.log (x / n)|) / (Real.pi * T) else 0) :=
    summable_of_ne_finset_zero (s := central x) (fun n hn => if_neg hn)
  have hsum := (summable_majorant a hx hxn hb hT ha).tsum_le_tsum
    (majorant_le_dyadic a hx hxn hb hT)
    ((ha.norm.mul_left (x ^ b / (Real.pi * T * Real.log 2))).add hfin)
  apply (norm_vertical_sub_sum_le a hx hxn hb hT ha).trans
  apply hsum.trans_eq
  rw [Summable.tsum_add (ha.norm.mul_left _) hfin, tsum_mul_left,
    tsum_eq_sum (s := central x) (fun n hn => if_neg hn)]
  rw [sum_ite_mem, inter_self, ← sum_div]
  unfold centralCost
  ring

theorem halfInteger_ne_nat (m n : ℕ) : (m : ℝ) + 1 / 2 ≠ n := by
  intro h
  have hmn : m < n := by exact_mod_cast (show (m : ℝ) < n by linarith)
  have hnm : n < m + 1 := by exact_mod_cast (show (n : ℝ) < (m + 1 : ℕ) by push_cast; linarith)
  omega

theorem floor_halfInteger (m : ℕ) : ⌊(m : ℝ) + 1 / 2⌋₊ = m := by
  apply Nat.floor_eq_iff (by positivity) |>.2
  constructor <;> linarith

end LiuWang.Proof.ExplicitPerron
