/-
! # Neutral divisor-count square bound for LCM-weight arguments

This module is the next layer of the neutral V1/V3 LCM-weight extraction.  It
reuses the already verified harmonic/multiples/reciprocal-LCM layer and keeps the
proof independent of the downstream Goldbach/Li--Liu/Fouvry application stack.
-/

import AnalyticNumberTheory.Sieve.LcmWeightBounds

namespace AnalyticNumberTheory.Sieve.LcmWeightBounds

open Finset Real

noncomputable section

/-- Neutral `τ(n)^2` prefix-sum bound used by both Pan V1 and V3.

The proof double-counts divisor pairs and then uses the shared reciprocal-LCM
bound.  It is intentionally kept under the neutral `LcmWeightBounds` namespace
until the existing V1/V3 public theorem names are redirected through wrappers.
-/
theorem divisorCountSq_sum_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ 2)) ≤
      (N : ℝ) * (1 + Real.log (N + 1)) ^ 3 := by
  have hsq : ∀ n : ℕ, ((n.divisors.card : ℝ) ^ 2) =
      ∑ d ∈ n.divisors, ∑ e ∈ n.divisors, (1 : ℝ) := by
    intro n
    have hc : (n.divisors.card : ℝ) = ∑ d ∈ n.divisors, (1 : ℝ) := by
      rw [Finset.card_eq_sum_ones]
      simp
    rw [hc, pow_two]
    rw [Finset.sum_mul (s := n.divisors) (f := fun _ : ℕ => (1 : ℝ))
      (a := ∑ e ∈ n.divisors, (1 : ℝ))]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    simp
  have hper : ∀ n ∈ Finset.Icc 1 N,
      (∑ d ∈ n.divisors, ∑ e ∈ n.divisors, (1 : ℝ)) =
        ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          (if Nat.lcm d e ∣ n then (1 : ℝ) else 0) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
    have hsub : n.divisors ⊆ Finset.Icc 1 N := by
      intro d hd
      rw [Finset.mem_Icc]
      have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
      constructor
      · exact Nat.pos_of_dvd_of_pos hdn hn1
      · exact le_trans (Nat.le_of_dvd hn1 hdn) hnN
    have hin : ∀ d : ℕ, d ∈ n.divisors →
        (∑ e ∈ n.divisors, (1 : ℝ)) =
          ∑ e ∈ Finset.Icc 1 N, (if Nat.lcm d e ∣ n then (1 : ℝ) else 0) := by
      intro d hd
      have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
      have hset : n.divisors =
          (Finset.Icc 1 N).filter (fun e => Nat.lcm d e ∣ n) := by
        ext e
        constructor
        · intro he
          have hen : e ∣ n := (Nat.mem_divisors.mp he).1
          rw [Finset.mem_filter, Finset.mem_Icc]
          refine ⟨⟨Nat.pos_of_dvd_of_pos hen hn1,
            le_trans (Nat.le_of_dvd hn1 hen) hnN⟩, ?_⟩
          exact (Nat.lcm_dvd_iff).2 ⟨hdn, hen⟩
        · intro he
          rw [Finset.mem_filter, Finset.mem_Icc] at he
          rcases he with ⟨⟨he1, heN⟩, hle⟩
          rw [Nat.mem_divisors]
          exact ⟨(Nat.lcm_dvd_iff.mp hle).2, Nat.ne_of_gt hn1⟩
      calc
        (∑ e ∈ n.divisors, (1 : ℝ)) =
            ∑ e ∈ (Finset.Icc 1 N).filter (fun e => Nat.lcm d e ∣ n), (1 : ℝ) := by
              rw [hset]
        _ = ∑ e ∈ Finset.Icc 1 N,
              (if Nat.lcm d e ∣ n then (1 : ℝ) else 0) := by
              rw [Finset.sum_filter]
    calc
      (∑ d ∈ n.divisors, ∑ e ∈ n.divisors, (1 : ℝ)) =
          ∑ d ∈ n.divisors, ∑ e ∈ Finset.Icc 1 N,
            (if Nat.lcm d e ∣ n then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro d hd
            exact hin d hd
      _ = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
            (if Nat.lcm d e ∣ n then (1 : ℝ) else 0) := by
            apply Finset.sum_subset hsub
            intro d hdIcc hdnot
            have hdn' : ¬ d ∣ n := by
              intro hdn
              apply hdnot
              rw [Nat.mem_divisors]
              exact ⟨hdn, Nat.ne_of_gt hn1⟩
            apply Finset.sum_eq_zero
            intro e he
            have hle : ¬ Nat.lcm d e ∣ n := by
              intro hle
              exact hdn' (dvd_trans (Nat.dvd_lcm_left d e) hle)
            simp [hle]
  calc
    (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ 2))
    = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, ∑ e ∈ n.divisors, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact hsq n
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          (if Nat.lcm d e ∣ n then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact hper n hn
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (if Nat.lcm d e ∣ n then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          ((N / Nat.lcm d e : ℕ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro d hd
          apply Finset.sum_congr rfl
          intro e he
          rw [Finset.sum_boole (p := fun n : ℕ => Nat.lcm d e ∣ n)
            (s := Finset.Icc 1 N)]
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
          have hlcm : 1 ≤ Nat.lcm d e :=
            le_trans hd1
              (Nat.le_lcm_left d
                (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1)
                  (Finset.mem_Icc.mp he).1))
          rw [card_multiples_Icc N (Nat.lcm d e) hlcm]
    _ ≤ ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          (N : ℝ) / (Nat.lcm d e : ℝ) := by
          apply Finset.sum_le_sum
          intro d hd
          apply Finset.sum_le_sum
          intro e he
          exact Nat.cast_div_le
    _ = (N : ℝ) *
          (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
            (1 : ℝ) / (Nat.lcm d e : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e he
          ring
    _ ≤ (N : ℝ) * (1 + Real.log (N + 1)) ^ 3 := by
          exact mul_le_mul_of_nonneg_left (lcm_inv_sum_le N)
            (by exact_mod_cast Nat.zero_le N)

end

end AnalyticNumberTheory.Sieve.LcmWeightBounds
