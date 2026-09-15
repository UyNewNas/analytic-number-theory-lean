/-
! # Neutral finite bounds for LCM-weight arguments

Reusable finite arithmetic lemmas shared by the Pan V1/V3 square-mean proofs.
This module deliberately has no dependency on the downstream Goldbach/Li--Liu
application layer.  The first slice extracts the harmonic-sum and multiples-count
lemmas; the LCM reciprocal sum and divisor-square sum are migrated only after
this neutral layer is independently checked.
-/

import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

namespace AnalyticNumberTheory.Sieve.LcmWeightBounds

open Finset Real

noncomputable section

/-- Harmonic sum on `Icc 1 M`: `Σ 1/k ≤ 1 + log (M+1)`. -/
theorem harmonic_Icc_le (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ)) ≤ 1 + Real.log (M + 1) := by
  have h1 : (∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ)) = (harmonic M : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp [one_div]
  calc
    (∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ)) = (harmonic M : ℝ) := h1
    _ ≤ 1 + Real.log (M : ℝ) := harmonic_le_one_add_log M
    _ ≤ 1 + Real.log (M + 1) := by
      by_cases hM0 : M = 0
      · subst M
        simp
      · have hMpos : 0 < (M : ℝ) := by
          exact_mod_cast (Nat.pos_of_ne_zero hM0)
        have hMle : (M : ℝ) ≤ (M + 1 : ℝ) := by norm_num
        exact add_le_add (le_refl (1 : ℝ)) (Real.log_le_log hMpos hMle)

/-- Multiples count on `Icc 1 N`: `#{n : m ∣ n} = N / m` for `m ≥ 1`. -/
theorem card_multiples_Icc (N m : ℕ) (hm : 1 ≤ m) :
    ((Finset.Icc 1 N).filter (fun n => m ∣ n)).card = N / m := by
  have hc := Nat.card_multiples N m
  have hbij : ((Finset.range N).filter (fun e => m ∣ e + 1)).card =
      ((Finset.Icc 1 N).filter (fun n => m ∣ n)).card := by
    apply Finset.card_bij (s := (Finset.range N).filter (fun e => m ∣ e + 1))
      (t := (Finset.Icc 1 N).filter (fun n => m ∣ n))
      (i := fun e _ => e + 1)
    · intro e he
      rw [Finset.mem_filter] at he
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_Icc]
        have he' : e < N := Finset.mem_range.mp he.1
        constructor <;> omega
      · exact he.2
    · intro a ha b hb h
      omega
    · intro n hn
      rw [Finset.mem_filter] at hn
      rcases hn with ⟨hnIcc, hmn⟩
      refine ⟨n - 1, ?_, ?_⟩
      · rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_range]
          have h1 : 1 ≤ n := (Finset.mem_Icc.mp hnIcc).1
          have hN : n ≤ N := (Finset.mem_Icc.mp hnIcc).2
          omega
        · have h1 : 1 ≤ n := (Finset.mem_Icc.mp hnIcc).1
          simpa [Nat.sub_add_cancel h1] using hmn
      · have h1 : 1 ≤ n := (Finset.mem_Icc.mp hnIcc).1
        omega
  rw [← hbij, hc]

end

end AnalyticNumberTheory.Sieve.LcmWeightBounds
