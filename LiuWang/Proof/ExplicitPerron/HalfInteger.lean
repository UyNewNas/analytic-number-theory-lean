import LiuWang.Proof.ExplicitPerron.Dyadic

/-!
# Half-integer distance sums
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace LiuWang.Proof.ExplicitPerron

def halfHarmonic (m : ℕ) : ℝ :=
  ∑ k ∈ range m, 1 / ((k : ℝ) + 1 / 2)

theorem halfHarmonic_succ (m : ℕ) :
    halfHarmonic (m + 1) = halfHarmonic m + 1 / ((m : ℝ) + 1 / 2) := by
  exact sum_range_succ _ _

theorem halfHarmonic_le (m : ℕ) :
    halfHarmonic (m + 1) ≤ 2 + (harmonic m : ℝ) := by
  induction m with
  | zero => norm_num [halfHarmonic]
  | succ m ih =>
    rw [halfHarmonic_succ, harmonic_succ]
    push_cast
    have hdiv : 1 / ((m : ℝ) + 1 + 1 / 2) ≤ 1 / ((m : ℝ) + 1) := by
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    simpa only [Nat.cast_add, Nat.cast_one] using (by
      simp only [one_div] at hdiv ⊢
      linarith : halfHarmonic (m + 1) + 1 / ((m : ℝ) + 1 + 1 / 2) ≤
        2 + ((harmonic m : ℝ) + ((m : ℝ) + 1)⁻¹))

theorem halfHarmonic_le_log (m : ℕ) :
    halfHarmonic (m + 1) ≤ 3 + Real.log (m + 1) := by
  have hm : (harmonic m : ℝ) ≤ harmonic (m + 1) := by
    rw [harmonic_succ]
    push_cast
    exact le_add_of_nonneg_right (by positivity)
  have h := harmonic_le_one_add_log (m + 1)
  push_cast at h
  linarith [halfHarmonic_le m]

theorem lower_distance_sum (m : ℕ) :
    (∑ n ∈ Icc 1 m, 1 / ((m : ℝ) + 1 / 2 - n)) = halfHarmonic m := by
  rw [← Ico_succ_right_eq_Icc, sum_Ico_eq_sum_range]
  change (∑ k ∈ range (m + 1 - 1),
    1 / ((m : ℝ) + 1 / 2 - ((1 + k : ℕ) : ℝ))) = _
  simp only [Nat.add_sub_cancel]
  calc
    _ = ∑ k ∈ range m, 1 / (((m - 1 - k : ℕ) : ℝ) + 1 / 2) := by
      apply sum_congr rfl
      intro k hk
      have hk' : k < m := mem_range.mp hk
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega),
        Nat.cast_sub (by omega), Nat.cast_one]
      congr 1
      ring
    _ = halfHarmonic m :=
      sum_range_reflect (fun k : ℕ => 1 / ((k : ℝ) + 1 / 2)) m

theorem upper_distance_sum (m : ℕ) :
    (∑ n ∈ Icc (m + 1) (2 * m + 1), 1 / ((n : ℝ) - ((m : ℝ) + 1 / 2))) =
      halfHarmonic (m + 1) := by
  rw [← Ico_succ_right_eq_Icc, sum_Ico_eq_sum_range]
  change (∑ k ∈ range (2 * m + 1 + 1 - (m + 1)),
    1 / (((m + 1 + k : ℕ) : ℝ) - ((m : ℝ) + 1 / 2))) = _
  have heq : 2 * m + 1 + 1 - (m + 1) = m + 1 := by omega
  rw [heq]
  apply sum_congr rfl
  intro k hk
  push_cast
  congr 1
  ring

theorem lower_log_distance {x y : ℝ} (hy : 0 < y) (hyx : y < x) :
    (x - y) / x ≤ |Real.log (x / y)| := by
  have hx : 0 < x := hy.trans hyx
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  have heq : Real.log (x / y) = -Real.log (y / x) := by
    rw [Real.log_div hx.ne' hy.ne', Real.log_div hy.ne' hx.ne']
    ring
  have hfrac : (x - y) / x = 1 - y / x := by field_simp
  rw [hfrac, heq]
  exact (by linarith : 1 - y / x ≤ -Real.log (y / x)).trans (le_abs_self _)

theorem upper_log_distance {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    (y - x) / y ≤ |Real.log (x / y)| := by
  have hy : 0 < y := hx.trans hxy
  have h := Real.log_le_sub_one_of_pos (div_pos hx hy)
  have hfrac : (y - x) / y = 1 - x / y := by field_simp
  rw [hfrac]
  exact (by linarith : 1 - x / y ≤ -Real.log (x / y)).trans (neg_le_abs _)

theorem lower_central_term {a : ℕ → ℂ} {A : ℝ → ℝ} {x b : ℝ} {n : ℕ}
    (hA : Monotone A) (ha : ‖a n‖ ≤ A n) (hn : 0 < n)
    (hnx : (n : ℝ) < x) (hnear : x / 2 < (n : ℝ)) (hb : 0 ≤ b) :
    ‖a n‖ * (x / n) ^ b / |Real.log (x / n)| ≤
      2 ^ b * A x * x * (1 / (x - n)) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hx : 0 < x := hn0.trans hnx
  have hcoef : ‖a n‖ ≤ A x := ha.trans (hA hnx.le)
  have hA0 : 0 ≤ A x := (norm_nonneg _).trans hcoef
  have hratio : x / n ≤ (2 : ℝ) := (div_le_iff₀ hn0).2 (by linarith)
  have hdist : 0 < (x - n) / x := div_pos (sub_pos.mpr hnx) hx
  calc
    _ ≤ A x * (2 : ℝ) ^ b / ((x - n) / x) := by
      gcongr
      exact lower_log_distance hn0 hnx
    _ = _ := by field_simp

theorem upper_central_term {a : ℕ → ℂ} {A : ℝ → ℝ} {x b : ℝ} {n : ℕ}
    (hA : Monotone A) (ha : ‖a n‖ ≤ A n) (hx : 0 < x)
    (hxn : x < (n : ℝ)) (hnear : (n : ℝ) ≤ 2 * x) (hb : 1 ≤ b) :
    ‖a n‖ * (x / n) ^ b / |Real.log (x / n)| ≤
      A (2 * x) * x * (1 / (n - x)) := by
  have hn0 : (0 : ℝ) < n := hx.trans hxn
  have hcoef : ‖a n‖ ≤ A (2 * x) := ha.trans (hA hnear)
  have hA0 : 0 ≤ A (2 * x) := (norm_nonneg _).trans hcoef
  have hdist : 0 < ((n : ℝ) - x) / n := div_pos (sub_pos.mpr hxn) hn0
  have hpow : (x / n) ^ b ≤ x / n :=
    Real.rpow_le_self_of_le_one (by positivity) ((div_le_one hn0).2 hxn.le) hb
  calc
    _ ≤ A (2 * x) * (x / n) / ((n - x) / n) := by
      gcongr
      · exact upper_log_distance hx hxn
    _ = _ := by field_simp

end LiuWang.Proof.ExplicitPerron
