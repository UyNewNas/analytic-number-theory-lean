import AnalyticNumberTheory.PrimeDistribution.PrimeNumberTheorem
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

namespace AnalyticNumberTheory.PrimeDistribution

open Asymptotics Filter Real
open scoped Nat.Prime

/-- The dyadic prime window `(P, 2P]`, packaged independently of any downstream application. -/
def dyadicPrimeWindow (P : ℕ) : Finset ℕ :=
  (Finset.Ioc P (2 * P)).filter Nat.Prime

@[simp] theorem mem_dyadicPrimeWindow {P p : ℕ} :
    p ∈ dyadicPrimeWindow P ↔ P < p ∧ p ≤ 2 * P ∧ p.Prime := by
  simp [dyadicPrimeWindow, and_assoc]

/-- The dyadic prime window is exactly the difference between the two standard prime finsets. -/
theorem dyadicPrimeWindow_eq_primesLE_sdiff (P : ℕ) :
    dyadicPrimeWindow P = Nat.primesLE (2 * P) \ Nat.primesLE P := by
  ext p
  simp only [mem_dyadicPrimeWindow, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨hPp, hp2P, hpprime⟩
    refine ⟨⟨hp2P, hpprime⟩, ?_⟩
    intro hpP
    exact (Nat.not_lt_of_ge hpP.1) hPp
  · rintro ⟨⟨hp2P, hpprime⟩, hpP⟩
    have hPp : P < p := by
      by_contra h
      exact hpP ⟨Nat.le_of_not_gt h, hpprime⟩
    exact ⟨hPp, hp2P, hpprime⟩

/-- Exact prime-counting formula for the size of a dyadic prime window. -/
theorem card_dyadicPrimeWindow (P : ℕ) :
    (dyadicPrimeWindow P).card = Nat.primeCounting (2 * P) - Nat.primeCounting P := by
  rw [dyadicPrimeWindow_eq_primesLE_sdiff]
  have hP : P ≤ 2 * P := by omega
  rw [Finset.card_sdiff_of_subset (Nat.primesLE_mono hP)]
  simp

/-- Bertrand's postulate makes every positive dyadic prime window nonempty. -/
theorem dyadicPrimeWindow_nonempty {P : ℕ} (hP : P ≠ 0) :
    (dyadicPrimeWindow P).Nonempty := by
  obtain ⟨p, hpprime, hPp, hp2P⟩ := Nat.exists_prime_lt_and_le_two_mul P hP
  exact ⟨p, (mem_dyadicPrimeWindow (P := P) (p := p)).2 ⟨hPp, hp2P, hpprime⟩⟩

/-- A reusable dyadic consequence of the prime number theorem: eventually the number of primes in
`(P, 2P]` is at least `P / (24 log P)`.  The deliberately coarse constant keeps the statement
stable while retaining the positive-order lower bound needed by downstream normalizations. -/
theorem eventually_dyadicPrimeWindow_card_lower_bound :
    ∀ᶠ P : ℕ in atTop,
      (1 / 24 : ℝ) * (P : ℝ) / log (P : ℝ) ≤ ((dyadicPrimeWindow P).card : ℝ) := by
  obtain ⟨c, hc, hcount⟩ := natPrimeCountingPNT
  have hsmall := hc.bound (by norm_num : (0 : ℝ) < 1 / 8)
  rcases eventually_atTop.1 hsmall with ⟨X, hX⟩
  filter_upwards [eventually_ge_atTop (max X 4)] with P hP
  have hXP : X ≤ P := le_trans (le_max_left X 4) hP
  have hX2P : X ≤ 2 * P := le_trans hXP (by omega)
  have hP4 : 4 ≤ P := le_trans (le_max_right X 4) hP
  have hcP := hX P hXP
  have hc2P := hX (2 * P) hX2P
  have hcP_abs : |c P| ≤ (1 / 8 : ℝ) := by
    simpa [Real.norm_eq_abs] using hcP
  have hc2P_abs : |c (2 * P)| ≤ (1 / 8 : ℝ) := by
    simpa [Real.norm_eq_abs] using hc2P
  have hP1 : (1 : ℝ) < P := by exact_mod_cast (by omega : 1 < P)
  have h2P1 : (1 : ℝ) < ((2 * P : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 < 2 * P)
  have hlogP : 0 < log (P : ℝ) := log_pos hP1
  have hlog2P : 0 < log ((2 * P : ℕ) : ℝ) := log_pos h2P1
  have h4P : (4 : ℝ) ≤ P := by exact_mod_cast hP4
  have hlog4le : log (4 : ℝ) ≤ log (P : ℝ) :=
    log_le_log (by norm_num) h4P
  have hlog4 : log (4 : ℝ) = 2 * log (2 : ℝ) := by
    calc
      log (4 : ℝ) = log ((2 : ℝ) * 2) := by norm_num
      _ = log (2 : ℝ) + log (2 : ℝ) := by
        rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      _ = 2 * log (2 : ℝ) := by ring
  have hlog2_le : log (2 : ℝ) ≤ (1 / 2 : ℝ) * log (P : ℝ) := by
    rw [hlog4] at hlog4le
    linarith
  have hlog2P_eq : log ((2 * P : ℕ) : ℝ) = log (2 : ℝ) + log (P : ℝ) := by
    norm_num [Nat.cast_mul]
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (P : ℝ) ≠ 0)]
  have hlog2P_le : log ((2 * P : ℕ) : ℝ) ≤ (3 / 2 : ℝ) * log (P : ℝ) := by
    rw [hlog2P_eq]
    linarith
  have hcP_low : (7 / 8 : ℝ) ≤ 1 + c P := by
    have hneg : -(1 / 8 : ℝ) ≤ c P := by
      linarith [neg_abs_le (c P), hcP_abs]
    linarith
  have hcP_high : 1 + c P ≤ (9 / 8 : ℝ) := by
    linarith [le_abs_self (c P), hcP_abs]
  have hc2P_low : (7 / 8 : ℝ) ≤ 1 + c (2 * P) := by
    have hneg : -(1 / 8 : ℝ) ≤ c (2 * P) := by
      linarith [neg_abs_le (c (2 * P)), hc2P_abs]
    linarith
  have hpiP_upper :
      (Nat.primeCounting P : ℝ) ≤ (9 / 8 : ℝ) * (P : ℝ) / log (P : ℝ) := by
    rw [hcount P]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcP_high (by positivity : 0 ≤ (P : ℝ)))
      (le_of_lt hlogP)
  have hpi2P_lower :
      (7 / 4 : ℝ) * (P : ℝ) / log ((2 * P : ℕ) : ℝ) ≤
        (Nat.primeCounting (2 * P) : ℝ) := by
    rw [hcount (2 * P)]
    have hmul :
        (7 / 4 : ℝ) * (P : ℝ) ≤ (1 + c (2 * P)) * ((2 * P : ℕ) : ℝ) := by
      norm_num [Nat.cast_mul]
      nlinarith [show (0 : ℝ) ≤ P by positivity]
    exact div_le_div_of_nonneg_right hmul (le_of_lt hlog2P)
  have hscaled_lower :
      (7 / 6 : ℝ) * (P : ℝ) / log (P : ℝ) ≤
        (7 / 4 : ℝ) * (P : ℝ) / log ((2 * P : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hlogP hlog2P]
    nlinarith [hlog2P_le, show (0 : ℝ) ≤ P by positivity]
  have hdiff :
      (1 / 24 : ℝ) * (P : ℝ) / log (P : ℝ) ≤
        (Nat.primeCounting (2 * P) : ℝ) - (Nat.primeCounting P : ℝ) := by
    have hpi2 :
        (7 / 6 : ℝ) * (P : ℝ) / log (P : ℝ) ≤
          (Nat.primeCounting (2 * P) : ℝ) :=
      le_trans hscaled_lower hpi2P_lower
    calc
      (1 / 24 : ℝ) * (P : ℝ) / log (P : ℝ) =
          (7 / 6 : ℝ) * (P : ℝ) / log (P : ℝ) -
            (9 / 8 : ℝ) * (P : ℝ) / log (P : ℝ) := by ring
      _ ≤ (Nat.primeCounting (2 * P) : ℝ) - (Nat.primeCounting P : ℝ) := by
        linarith
  have hpi_mono : Nat.primeCounting P ≤ Nat.primeCounting (2 * P) := by
    have hsubset := Nat.primesLE_mono (show P ≤ 2 * P by omega)
    have hcard := Finset.card_le_card hsubset
    simpa using hcard
  have hcard_real :
      ((dyadicPrimeWindow P).card : ℝ) =
        (Nat.primeCounting (2 * P) : ℝ) - (Nat.primeCounting P : ℝ) := by
    rw [card_dyadicPrimeWindow, Nat.cast_sub hpi_mono]
  rw [hcard_real]
  exact hdiff

end AnalyticNumberTheory.PrimeDistribution