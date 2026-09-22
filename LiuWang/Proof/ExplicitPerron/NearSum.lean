import LiuWang.Proof.ExplicitPerron.HalfInteger

/-!
# Summing the half-integer central range

The envelope is a monotone function on the real line. Thus its occurrences
at `x` and `2*x` have the same type as the coefficient bounds at natural casts.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace LiuWang.Proof.ExplicitPerron

theorem centralCost_halfInteger_le (a : ℕ → ℂ) (A : ℝ → ℝ)
    (hA : Monotone A) (ha : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ A n)
    {m : ℕ} (hm : 1 ≤ m) {b : ℝ} (hb : 1 ≤ b) :
    centralCost a ((m : ℝ) + 1 / 2) b ≤
      2 ^ b * A ((m : ℝ) + 1 / 2) * ((m : ℝ) + 1 / 2) * halfHarmonic m +
      A (2 * ((m : ℝ) + 1 / 2)) * ((m : ℝ) + 1 / 2) * halfHarmonic (m + 1) := by
  let x : ℝ := (m : ℝ) + 1 / 2
  let B : ℝ := 2 ^ b * A x * x
  let D : ℝ := A (2 * x) * x
  let g : ℕ → ℝ := fun n =>
    if n ≤ m then B * (1 / (x - n)) else D * (1 / (n - x))
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx : 0 < x := by dsimp [x]; positivity
  have hx1 : 1 ≤ x := by dsimp [x]; linarith
  have hA1 : 0 ≤ A 1 := (norm_nonneg (a 1)).trans (by simpa using ha 1 le_rfl)
  have hAx : 0 ≤ A x := hA1.trans (hA hx1)
  have hA2x : 0 ≤ A (2 * x) := hA1.trans (hA (by linarith))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hfloor : ⌊2 * x⌋₊ = 2 * m + 1 := by
    have heq : 2 * x = ((2 * m + 1 : ℕ) : ℝ) := by dsimp [x]; push_cast; ring
    rw [heq, Nat.floor_natCast]
  have hsub : central x ⊆ Ico 1 (2 * m + 2) := by
    intro n hn
    have hn' := mem_Icc.mp (mem_filter.mp hn).1
    rw [hfloor] at hn'
    exact mem_Ico.mpr ⟨hn'.1, by omega⟩
  have hg (n : ℕ) (hn : n ∈ Ico 1 (2 * m + 2)) : 0 ≤ g n := by
    dsimp [g]
    split_ifs with h
    · have hnR : (n : ℝ) ≤ m := by exact_mod_cast h
      have : 0 < x - n := by dsimp [x]; linarith
      positivity
    · have hnR : (m : ℝ) + 1 ≤ n := by exact_mod_cast (show m + 1 ≤ n by omega)
      have : 0 < (n : ℝ) - x := by dsimp [x]; linarith
      positivity
  have hcentral : centralCost a x b ≤ ∑ n ∈ central x, g n := by
    apply sum_le_sum
    intro n hn
    have hn' := mem_Icc.mp (mem_filter.mp hn).1
    have hnear := (mem_filter.mp hn).2
    dsimp [g]
    split_ifs with h
    · have hnR : (n : ℝ) ≤ m := by exact_mod_cast h
      exact lower_central_term hA (ha n hn'.1) hn'.1
        (by dsimp [x]; linarith) hnear (by linarith)
    · have hnR : (m : ℝ) + 1 ≤ n := by exact_mod_cast (show m + 1 ≤ n by omega)
      exact upper_central_term hA (ha n hn'.1) hx
        (by dsimp [x]; linarith) ((Nat.le_floor_iff (by positivity)).1 hn'.2) hb
  have hlo : (∑ n ∈ Ico 1 (m + 1), g n) = B * halfHarmonic m := by
    rw [← lower_distance_sum, mul_sum]
    apply sum_congr rfl
    intro n hn
    have hnm : n ≤ m := by have := (mem_Ico.mp hn).2; omega
    simp only [g, hnm, if_true]
    rfl
  have hhi : (∑ n ∈ Ico (m + 1) (2 * m + 2), g n) = D * halfHarmonic (m + 1) := by
    rw [← upper_distance_sum, mul_sum]
    apply sum_congr rfl
    intro n hn
    have hnm : ¬ n ≤ m := by have := (mem_Ico.mp hn).1; omega
    simp only [g, hnm, if_false]
    rfl
  calc
    centralCost a x b ≤ ∑ n ∈ central x, g n := hcentral
    _ ≤ ∑ n ∈ Ico 1 (2 * m + 2), g n :=
      sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => hg n hn)
    _ = (∑ n ∈ Ico 1 (m + 1), g n) +
        ∑ n ∈ Ico (m + 1) (2 * m + 2), g n :=
      (sum_Ico_consecutive g (by omega) (by omega)).symm
    _ = _ := by rw [hlo, hhi]

end LiuWang.Proof.ExplicitPerron
