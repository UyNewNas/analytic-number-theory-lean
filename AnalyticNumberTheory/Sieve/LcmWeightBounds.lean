/-
! # Neutral finite bounds for LCM-weight arguments

Reusable finite arithmetic lemmas shared by the Pan V1/V3 square-mean proofs.
This module deliberately has no dependency on the downstream Goldbach/Li--Liu
application layer.  The extraction is staged so each neutral layer is checked by
the normal repository-wide build and trust audit before existing public wrappers
are redirected to it.
-/

import Mathlib.Data.Nat.Totient
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

/-- Internal normalization `1/lcm(d,e) = gcd(d,e)/(d*e)` for positive naturals. -/
private lemma lcm_inv_eq_gcd_div {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) :
    (1 : ℝ) / (Nat.lcm d e : ℝ) = (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ)) := by
  have hgmul : (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ) = (d : ℝ) * (e : ℝ) := by
    exact_mod_cast (Nat.gcd_mul_lcm d e)
  have hne_d : (d : ℝ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd).ne'
  have hne_e : (e : ℝ) ≠ 0 := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) he).ne'
  have hne_g : (Nat.gcd d e : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_left e (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd)).ne'
  have hne_l : (Nat.lcm d e : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.lcm_pos (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd)
      (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) he)).ne'
  field_simp [hne_d, hne_e, hne_g, hne_l]
  rw [mul_comm (Nat.lcm d e : ℝ)]
  exact hgmul.symm

/-- Neutral reciprocal-LCM double-sum bound used by both Pan V1 and V3. -/
theorem lcm_inv_sum_le (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (Nat.lcm d e : ℝ)) ≤
      (1 + Real.log (N + 1)) ^ 3 := by
  have hH : ∀ M : ℕ, M ≤ N →
      (∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ)) ≤ 1 + Real.log (N + 1) := by
    intro M hMN
    calc
      (∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ)) ≤ 1 + Real.log (M + 1) := harmonic_Icc_le M
      _ ≤ 1 + Real.log (N + 1) := by
        have hle : M + 1 ≤ N + 1 := Nat.succ_le_succ hMN
        have hpos : 0 < (M + 1 : ℕ) := Nat.succ_pos M
        exact add_le_add (le_refl (1 : ℝ))
          (Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle))
  have hstep1 : (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (Nat.lcm d e : ℝ)) =
      (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ))) := by
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    exact lcm_inv_eq_gcd_div (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
  have htot : ∀ d e : ℕ,
      (Nat.gcd d e : ℝ) = ∑ g ∈ (Nat.gcd d e).divisors, (Nat.totient g : ℝ) := by
    intro d e
    conv_lhs => rw [← Nat.sum_totient (Nat.gcd d e)]
    rw [Nat.cast_sum]
  have hstep2 : (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ))) =
      (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ∑ g ∈ (Nat.gcd d e).divisors, (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ))) := by
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    rw [htot d e, Finset.sum_div]
  have hstep3 : (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ∑ g ∈ (Nat.gcd d e).divisors, (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ))) =
      (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ∑ g ∈ Finset.Icc 1 N, (if g ∣ d ∧ g ∣ e then
          (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0)) := by
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    have hset : (Nat.gcd d e).divisors =
        (Finset.Icc 1 N).filter (fun g => g ∣ d ∧ g ∣ e) := by
      ext g
      constructor
      · intro hgm
        rw [Finset.mem_filter, Finset.mem_Icc]
        rw [Nat.mem_divisors] at hgm
        rcases hgm with ⟨hgcd, hg0⟩
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
        have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
        have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgcd
          (Nat.gcd_pos_of_pos_left e (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd1))
        have hgN : g ≤ N := le_trans (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left e
          (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd1)) hgcd)
          (le_trans (Nat.le_of_dvd (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd1)
            (Nat.gcd_dvd_left d e)) (Finset.mem_Icc.mp hd).2)
        refine ⟨⟨hgpos, hgN⟩, ?_⟩
        exact ⟨dvd_trans hgcd (Nat.gcd_dvd_left d e), dvd_trans hgcd (Nat.gcd_dvd_right d e)⟩
      · intro hgm
        rw [Finset.mem_filter, Finset.mem_Icc] at hgm
        rcases hgm with ⟨⟨hg1, hgN⟩, hgde⟩
        rw [Nat.mem_divisors]
        constructor
        · exact Nat.dvd_gcd hgde.1 hgde.2
        · exact (Nat.gcd_pos_of_pos_left e (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1)
            (Finset.mem_Icc.mp hd).1)).ne'
    rw [← Finset.sum_filter (s := Finset.Icc 1 N) (p := fun g => g ∣ d ∧ g ∣ e)
      (f := fun g => (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ)))]
    rw [hset]
  have hstep4 : (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        ∑ g ∈ Finset.Icc 1 N, (if g ∣ d ∧ g ∣ e then
          (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0)) =
      (∑ g ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        (if g ∣ d ∧ g ∣ e then (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0)) := by
    let F : ℕ → ℕ → ℕ → ℝ := fun d e g =>
      if g ∣ d ∧ g ∣ e then (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0
    have hswap1 : (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, ∑ g ∈ Finset.Icc 1 N, F d e g) =
        (∑ d ∈ Finset.Icc 1 N, ∑ g ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, F d e g) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.sum_comm (s := Finset.Icc 1 N) (t := Finset.Icc 1 N) (f := fun e g => F d e g)
    have hswap2 : (∑ d ∈ Finset.Icc 1 N, ∑ g ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, F d e g) =
        (∑ g ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, F d e g) := by
      exact Finset.sum_comm (s := Finset.Icc 1 N) (t := Finset.Icc 1 N)
        (f := fun d g => ∑ e ∈ Finset.Icc 1 N, F d e g)
    exact hswap1.trans hswap2
  have hfixed : ∀ g : ℕ, g ∈ Finset.Icc 1 N →
      (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        (if g ∣ d ∧ g ∣ e then (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0)) =
      (Nat.totient g : ℝ) / (g : ℝ) ^ 2 *
        (∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) *
        (∑ e ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (e : ℝ)) := by
    intro g hg
    have hg1 : 1 ≤ g := (Finset.mem_Icc.mp hg).1
    have hgpos : 0 < (g : ℝ) := by exact_mod_cast hg1
    have hfac : ∀ d e : ℕ, 1 ≤ d → 1 ≤ e →
        (if g ∣ d ∧ g ∣ e then (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0) =
          (Nat.totient g : ℝ) * (if g ∣ d then (1 : ℝ) / (d : ℝ) else 0) *
            (if g ∣ e then (1 : ℝ) / (e : ℝ) else 0) := by
      intro d e hd he
      by_cases hgd : g ∣ d <;> by_cases hge : g ∣ e <;> simp [hgd, hge]
      · field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd).ne',
          show (e : ℝ) ≠ 0 by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) he).ne']
    have hmultiples : ∀ g : ℕ, 1 ≤ g →
        (∑ d ∈ Finset.Icc 1 N, (if g ∣ d then (1 : ℝ) / (d : ℝ) else 0)) =
          (1 : ℝ) / (g : ℝ) * (∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) := by
      intro g hg1
      have hg1pos : 0 < g := hg1
      rw [← Finset.sum_filter (s := Finset.Icc 1 N) (p := fun d => g ∣ d)
        (f := fun d => (1 : ℝ) / (d : ℝ))]
      calc
        (∑ d ∈ (Finset.Icc 1 N).filter (fun d => g ∣ d), (1 : ℝ) / (d : ℝ))
            = ∑ d' ∈ Finset.Icc 1 (N / g), (1 : ℝ) / ((g * d' : ℕ) : ℝ) := by
                apply Finset.sum_bij (s := (Finset.Icc 1 N).filter (fun d => g ∣ d))
                  (t := Finset.Icc 1 (N / g))
                  (f := fun d => (1 : ℝ) / (d : ℝ))
                  (g := fun d' => (1 : ℝ) / ((g * d' : ℕ) : ℝ))
                  (i := fun d _ => d / g)
                · intro d hd
                  rw [Finset.mem_filter] at hd
                  rcases hd with ⟨hdIcc, hgd⟩
                  rw [Finset.mem_Icc]
                  constructor
                  · have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
                    exact Nat.div_pos (Nat.le_of_dvd (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd1) hgd) hg1pos
                  · exact Nat.div_le_div_right (Finset.mem_Icc.mp hdIcc).2
                · intro a ha b hb h
                  have hga : g ∣ a := (Finset.mem_filter.mp ha).2
                  have hgb : g ∣ b := (Finset.mem_filter.mp hb).2
                  calc
                    a = g * (a / g) := (Nat.mul_div_cancel' hga).symm
                    _ = g * (b / g) := by rw [h]
                    _ = b := Nat.mul_div_cancel' hgb
                · intro d' hd'
                  rw [Finset.mem_Icc] at hd'
                  rcases hd' with ⟨hd'1, hd'N⟩
                  refine ⟨g * d', ?_, ?_⟩
                  · rw [Finset.mem_filter]
                    constructor
                    · rw [Finset.mem_Icc]
                      constructor
                      · exact le_trans hg1 (Nat.le_mul_of_pos_right g (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd'1))
                      · have hle : d' * g ≤ N := (Nat.le_div_iff_mul_le hg1pos).mp hd'N
                        simpa [Nat.mul_comm] using hle
                    · exact dvd_mul_right g d'
                  · exact Nat.mul_div_right d' hg1pos
                · intro d hd
                  have hgd : g ∣ d := (Finset.mem_filter.mp hd).2
                  rw [Nat.mul_div_cancel' hgd]
        _ = (1 : ℝ) / (g : ℝ) * (∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro d hd
              have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
              field_simp [hgpos.ne',
                show (d : ℝ) ≠ 0 by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hd1).ne']
              rw [Nat.cast_mul]
    calc
      (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
          (if g ∣ d ∧ g ∣ e then (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0))
          = (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
              (Nat.totient g : ℝ) * (if g ∣ d then (1 : ℝ) / (d : ℝ) else 0) *
                (if g ∣ e then (1 : ℝ) / (e : ℝ) else 0)) := by
            apply Finset.sum_congr rfl
            intro d hd
            apply Finset.sum_congr rfl
            intro e he
            exact hfac d e (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
      _ = (Nat.totient g : ℝ) *
            (∑ d ∈ Finset.Icc 1 N, (if g ∣ d then (1 : ℝ) / (d : ℝ) else 0)) *
            (∑ e ∈ Finset.Icc 1 N, (if g ∣ e then (1 : ℝ) / (e : ℝ) else 0)) := by
            let B : ℕ → ℝ := fun d => if g ∣ d then (1 : ℝ) / (d : ℝ) else 0
            let C : ℕ → ℝ := fun e => if g ∣ e then (1 : ℝ) / (e : ℝ) else 0
            calc
              (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, ((Nat.totient g : ℝ) * B d) * C e)
                  = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, (Nat.totient g : ℝ) * (B d * C e) := by
                    apply Finset.sum_congr rfl
                    intro d hd
                    apply Finset.sum_congr rfl
                    intro e he
                    ring
              _ = (Nat.totient g : ℝ) * (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, B d * C e) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro d hd
                    rw [Finset.mul_sum]
              _ = (Nat.totient g : ℝ) * ((∑ d ∈ Finset.Icc 1 N, B d) * (∑ e ∈ Finset.Icc 1 N, C e)) := by
                    congr 1
                    calc
                      (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, B d * C e)
                          = ∑ d ∈ Finset.Icc 1 N, B d * (∑ e ∈ Finset.Icc 1 N, C e) := by
                                apply Finset.sum_congr rfl
                                intro d hd
                                rw [← Finset.mul_sum (s := Finset.Icc 1 N) (f := fun e => C e) (a := B d)]
                      _ = (∑ d ∈ Finset.Icc 1 N, B d) * (∑ e ∈ Finset.Icc 1 N, C e) := by
                                rw [← Finset.sum_mul (s := Finset.Icc 1 N) (f := fun d => B d)
                                  (a := (∑ e ∈ Finset.Icc 1 N, C e))]
              _ = ((Nat.totient g : ℝ) * ∑ d ∈ Finset.Icc 1 N, B d) * (∑ e ∈ Finset.Icc 1 N, C e) := by ring
      _ = (Nat.totient g : ℝ) / (g : ℝ) ^ 2 *
            (∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) *
            (∑ e ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (e : ℝ)) := by
            rw [hmultiples g hg1]
            field_simp [hgpos.ne']
  calc
    (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (Nat.lcm d e : ℝ))
    = (∑ g ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
        (if g ∣ d ∧ g ∣ e then (Nat.totient g : ℝ) / ((d : ℝ) * (e : ℝ)) else 0)) := by
          rw [hstep1, hstep2, hstep3, hstep4]
    _ = (∑ g ∈ Finset.Icc 1 N, (Nat.totient g : ℝ) / (g : ℝ) ^ 2 *
        (∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) *
        (∑ e ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (e : ℝ))) := by
          apply Finset.sum_congr rfl
          intro g hg
          exact hfixed g hg
    _ ≤ (∑ g ∈ Finset.Icc 1 N, (1 : ℝ) / (g : ℝ) * (1 + Real.log (N + 1)) ^ 2) := by
          apply Finset.sum_le_sum
          intro g hg
          have hg1 : 1 ≤ g := (Finset.mem_Icc.mp hg).1
          have hHg : (∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) ≤ 1 + Real.log (N + 1) :=
            hH (N / g) (Nat.div_le_self N g)
          have hphi : (Nat.totient g : ℝ) / (g : ℝ) ^ 2 ≤ (1 : ℝ) / (g : ℝ) := by
            have htg : Nat.totient g ≤ g := Nat.totient_le g
            have hgpos : 0 < (g : ℝ) := by exact_mod_cast hg1
            calc
              (Nat.totient g : ℝ) / (g : ℝ) ^ 2 ≤ (g : ℝ) / (g : ℝ) ^ 2 := by
                    exact div_le_div_of_nonneg_right (by exact_mod_cast htg) (sq_nonneg _)
              _ = (1 : ℝ) / (g : ℝ) := by field_simp [hgpos.ne']
          have h1 : (Nat.totient g : ℝ) / (g : ℝ) ^ 2 * (1 + Real.log (N + 1)) ^ 2 ≤
              (1 : ℝ) / (g : ℝ) * (1 + Real.log (N + 1)) ^ 2 := by
            exact mul_le_mul_of_nonneg_right hphi (sq_nonneg _)
          calc
            (Nat.totient g : ℝ) / (g : ℝ) ^ 2 *
                (∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) *
                (∑ e ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (e : ℝ))
                ≤ (Nat.totient g : ℝ) / (g : ℝ) ^ 2 * (1 + Real.log (N + 1)) ^ 2 := by
                      have hcoef : 0 ≤ (Nat.totient g : ℝ) / (g : ℝ) ^ 2 := by positivity
                      have hHnonneg : 0 ≤ (∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) := by
                        exact Finset.sum_nonneg (fun _ _ => div_nonneg zero_le_one (by positivity))
                      have hclog : 0 ≤ 1 + Real.log (N + 1) := by
                        have hlog : 0 ≤ Real.log (N + 1) :=
                          Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 1 by omega))
                        linarith
                      have hHmul : (∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) *
                            (∑ e ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (e : ℝ)) ≤
                          (1 + Real.log (N + 1)) * (1 + Real.log (N + 1)) := by
                        exact mul_le_mul hHg hHg hHnonneg hclog
                      calc
                        (Nat.totient g : ℝ) / (g : ℝ) ^ 2 *
                            (∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) *
                            (∑ e ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (e : ℝ))
                            = (Nat.totient g : ℝ) / (g : ℝ) ^ 2 *
                              ((∑ d ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (d : ℝ)) *
                                (∑ e ∈ Finset.Icc 1 (N / g), (1 : ℝ) / (e : ℝ))) := by ring
                        _ ≤ (Nat.totient g : ℝ) / (g : ℝ) ^ 2 *
                              ((1 + Real.log (N + 1)) * (1 + Real.log (N + 1))) := by
                              exact mul_le_mul_of_nonneg_left hHmul hcoef
                        _ = (Nat.totient g : ℝ) / (g : ℝ) ^ 2 * (1 + Real.log (N + 1)) ^ 2 := by
                              rw [← pow_two]
            _ ≤ (1 : ℝ) / (g : ℝ) * (1 + Real.log (N + 1)) ^ 2 := h1
    _ = (1 + Real.log (N + 1)) ^ 2 * (∑ g ∈ Finset.Icc 1 N, (1 : ℝ) / (g : ℝ)) := by
          rw [← Finset.sum_mul (s := Finset.Icc 1 N)
            (f := fun g => (1 : ℝ) / (g : ℝ)) (a := (1 + Real.log (N + 1)) ^ 2)]
          ring
    _ ≤ (1 + Real.log (N + 1)) ^ 2 * (1 + Real.log (N + 1)) := by
          exact mul_le_mul_of_nonneg_left (harmonic_Icc_le N) (sq_nonneg _)
    _ = (1 + Real.log (N + 1)) ^ 3 := by ring

end

end AnalyticNumberTheory.Sieve.LcmWeightBounds
