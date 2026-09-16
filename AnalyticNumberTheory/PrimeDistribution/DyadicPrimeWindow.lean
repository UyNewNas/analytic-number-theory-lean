import AnalyticNumberTheory.PrimeDistribution.PrimeNumberTheorem
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

namespace AnalyticNumberTheory.PrimeDistribution

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

end AnalyticNumberTheory.PrimeDistribution
