import AnalyticNumberTheory.LargeSieve.CharacterIndicators
import Mathlib.Tactic

open scoped BigOperators
open Classical

namespace AnalyticNumberTheory
namespace Dirichlet

noncomputable section

/-- Dirichlet-character orthogonality in conjugated form on unit residue classes.
This is a namespace-local reusable facade over ANT's already-audited large-sieve API. -/
theorem charOrthSumUnit
    {q : ℕ} (hq : 0 < q) {a b : ZMod q} (ha : IsUnit a) (hb : IsUnit b) :
    (∑ χ : DirichletCharacter ℂ q, χ a * star (χ b)) =
      if a = b then (q.totient : ℂ) else 0 :=
  LargeSieve.charOrthSum_unit hq ha hb

/-- Three-factor character kernel obtained from multiplicativity and the existing ANT
Dirichlet-character orthogonality theorem. -/
theorem charOrthMulKernel
    {q : ℕ} (hq : 0 < q) {a b c : ZMod q}
    (ha : IsUnit a) (hb : IsUnit b) (hc : IsUnit c) :
    (∑ χ : DirichletCharacter ℂ q, χ a * χ b * star (χ c)) =
      if a * b = c then (q.totient : ℂ) else 0 := by
  have hab : IsUnit (a * b) := ha.mul hb
  calc
    (∑ χ : DirichletCharacter ℂ q, χ a * χ b * star (χ c)) =
        ∑ χ : DirichletCharacter ℂ q, χ (a * b) * star (χ c) := by
          apply Finset.sum_congr rfl
          intro χ _hχ
          rw [map_mul]
    _ = if a * b = c then (q.totient : ℂ) else 0 :=
      charOrthSumUnit hq hab hc

/-- Prime-modulus natural-number specialization of the three-factor kernel. -/
theorem charOrthMulKernel_prime
    {N p n m : ℕ} (hN : N.Prime)
    (hp0 : 0 < p) (hpN : p < N)
    (hn0 : 0 < n) (hnN : n < N)
    (hm0 : 0 < m) (hmN : m < N) :
    (∑ χ : DirichletCharacter ℂ N,
      χ (p : ZMod N) * χ (n : ZMod N) * star (χ (m : ZMod N))) =
      if p * n ≡ m [MOD N] then ((N - 1 : ℕ) : ℂ) else 0 := by
  have hpunit : IsUnit (p : ZMod N) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hN).2
      (Nat.not_dvd_of_pos_of_lt hp0 hpN)).symm
  have hnunit : IsUnit (n : ZMod N) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hN).2
      (Nat.not_dvd_of_pos_of_lt hn0 hnN)).symm
  have hmunit : IsUnit (m : ZMod N) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hN).2
      (Nat.not_dvd_of_pos_of_lt hm0 hmN)).symm
  have hiff :
      (p : ZMod N) * (n : ZMod N) = (m : ZMod N) ↔ p * n ≡ m [MOD N] := by
    simpa only [Nat.cast_mul] using (ZMod.natCast_eq_natCast_iff (p * n) m N)
  rw [charOrthMulKernel hN.pos hpunit hnunit hmunit, Nat.totient_prime hN]
  by_cases hmod : p * n ≡ m [MOD N]
  · rw [if_pos (hiff.mpr hmod), if_pos hmod]
  · rw [if_neg (fun h => hmod (hiff.mp h)), if_neg hmod]

/-- Prime-modulus natural-number specialization of the two-factor orthogonality kernel.
For positive representatives strictly below the prime modulus, congruence is literal equality. -/
theorem charOrthKernel_prime_two
    {N p q : ℕ} (hN : N.Prime)
    (hp0 : 0 < p) (hpN : p < N)
    (hq0 : 0 < q) (hqN : q < N) :
    (∑ χ : DirichletCharacter ℂ N,
      χ (p : ZMod N) * star (χ (q : ZMod N))) =
      if p = q then ((N - 1 : ℕ) : ℂ) else 0 := by
  have hpunit : IsUnit (p : ZMod N) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hN).2
      (Nat.not_dvd_of_pos_of_lt hp0 hpN)).symm
  have hqunit : IsUnit (q : ZMod N) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hN).2
      (Nat.not_dvd_of_pos_of_lt hq0 hqN)).symm
  have hiff : ((p : ZMod N) = (q : ZMod N)) ↔ p = q := by
    constructor
    · intro h
      have hmod : p ≡ q [MOD N] :=
        (ZMod.natCast_eq_natCast_iff p q N).mp h
      exact hmod.eq_of_lt_of_lt hpN hqN
    · intro h
      simpa [h]
  rw [charOrthSumUnit hN.pos hpunit hqunit, Nat.totient_prime hN]
  by_cases hpq : p = q
  · simp [hpq, hiff]
  · simp [hpq, hiff]

end
end Dirichlet
end AnalyticNumberTheory
