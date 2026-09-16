import AnalyticNumberTheory.Dirichlet.Orthogonality
import Mathlib.Tactic

open scoped BigOperators
open Classical

namespace AnalyticNumberTheory
namespace Dirichlet

noncomputable section

/-- The finite set of nonprincipal Dirichlet characters modulo `N`. -/
def nonprincipalCharacters (N : ℕ) : Finset (DirichletCharacter ℂ N) :=
  Finset.univ.erase 1

@[simp] theorem mem_nonprincipalCharacters
    {N : ℕ} {χ : DirichletCharacter ℂ N} :
    χ ∈ nonprincipalCharacters N ↔ χ ≠ 1 := by
  simp [nonprincipalCharacters]

/-- Exact principal/nonprincipal splitting of a finite sum over all Dirichlet characters. -/
theorem sum_chars_eq_principal_add_nonprincipal
    {N : ℕ} (F : DirichletCharacter ℂ N → ℂ) :
    (∑ χ : DirichletCharacter ℂ N, F χ) =
      F 1 + ∑ χ in nonprincipalCharacters N, F χ := by
  classical
  rw [← Finset.sum_erase_add (Finset.univ : Finset (DirichletCharacter ℂ N)) F
    (Finset.mem_univ (1 : DirichletCharacter ℂ N)), add_comm]
  rfl

/-- At a prime modulus, on positive representatives below the modulus, the nonprincipal
three-factor kernel is the full orthogonality incidence mass minus the principal contribution `1`. -/
theorem charOrthMulKernel_prime_nonprincipal
    {N p n m : ℕ} (hN : N.Prime)
    (hp0 : 0 < p) (hpN : p < N)
    (hn0 : 0 < n) (hnN : n < N)
    (hm0 : 0 < m) (hmN : m < N) :
    (∑ χ in nonprincipalCharacters N,
      χ (p : ZMod N) * χ (n : ZMod N) * star (χ (m : ZMod N))) =
      (if p * n ≡ m [MOD N] then ((N - 1 : ℕ) : ℂ) else 0) - 1 := by
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
  let F : DirichletCharacter ℂ N → ℂ := fun χ =>
    χ (p : ZMod N) * χ (n : ZMod N) * star (χ (m : ZMod N))
  have hsplit := sum_chars_eq_principal_add_nonprincipal (N := N) F
  have hpone : (1 : DirichletCharacter ℂ N) (p : ZMod N) = 1 :=
    MulChar.one_apply hpunit
  have hnone : (1 : DirichletCharacter ℂ N) (n : ZMod N) = 1 :=
    MulChar.one_apply hnunit
  have hmone : (1 : DirichletCharacter ℂ N) (m : ZMod N) = 1 :=
    MulChar.one_apply hmunit
  have hprincipal : F 1 = 1 := by simp [F, hpone, hnone, hmone]
  have hsum :
      (∑ χ in nonprincipalCharacters N, F χ) + 1 =
        ∑ χ : DirichletCharacter ℂ N, F χ := by
    rw [← hprincipal]
    simpa [add_comm] using hsplit.symm
  have hnonprincipal := eq_sub_of_add_eq hsum
  have hall := charOrthMulKernel_prime
    (N := N) (p := p) (n := n) (m := m) hN
    hp0 hpN hn0 hnN hm0 hmN
  rw [all] at hnonprincipal
  exact hnonprincipal

/-- Weighted finite collapse of the full three-factor character kernel at a prime modulus. -/
theorem weightedCharKernelCollapse_prime
    {N : ℕ} (hN : N.Prime)
    {S T U : Finset ℕ}
    (hS : ∀ p ∈ S, 0 < p ∧ p < N)
    (hT : ∀ n ∈ T, 0 < n ∧ n < N)
    (hU : ∀ m ∈ U, 0 < m ∧ m < N)
    (w : ℕ → ℕ → ℕ → ℂ) :
    (∑ p ∈ S, ∑ n ∈ T, ∑ m ∈ U,
      w p n m *
        (∑ χ : DirichletCharacter ℂ N,
          χ (p : ZMod N) * χ (n : ZMod N) * star (χ (m : ZMod N)))) =
      ∑ p ∈ S, ∑ n ∈ T, ∑ m ∈ U,
        if p * n ≡ m [MOD N]
        then w p n m * (((N - 1 : ℕ) : ℂ))
        else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  rw [charOrthMulKernel_prime
    (N := N) (p := p) (n := n) (m := m) hN
    (hS p hp).1 (hS p hp).2
    (hT n hn).1 (hT n hn).2
    (hU m hm).1 (hU m hm).2]
  by_cases hmod : p * n ≡ m [MOD N] <;> simp [hmod]

/-- On the same prime-modulus range, the principal-character part of an arbitrary weighted
triple expansion is exactly the total weight. -/
theorem weightedPrincipalKernel_prime
    {N : ℕ} (hN : N.Prime)
    {S T U : Finset ℕ}
    (hS : ∀ p ∈ S, 0 < p ∧ p < N)
    (hT : ∀ n ∈ T, 0 < n ∧ n < N)
    (hU : ∀ m ∈ U, 0 < m ∧ m < N)
    (w : ℕ → ℕ → ℕ → ℂ) :
    (∑ p ∈ S, ∑ n ∈ T, ∑ m ∈ U,
      w p n m *
        ((1 : DirichletCharacter ℂ N) (p : ZMod N) *
          (1 : DirichletCharacter ℂ N) (n : ZMod N) *
          star ((1 : DirichletCharacter ℂ N) (m : ZMod N)))) =
      ∑ p ∈ S, ∑ n ∈ T, ∑ m ∈ U, w p n m := by
  classical
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  have hpunit : IsUnit (p : ZMod N) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hN).2
      (Nat.not_dvd_of_pos_of_lt (hS p hp).1 (hS p hp).2)).symm
  have hnunit : IsUnit (n : ZMod N) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hN).2
      (Nat.not_dvd_of_pos_of_lt (hT n hn).1 (hT n hn).2)).symm
  have hmunit : IsUnit (m : ZMod N) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hN).2
      (Nat.not_dvd_of_pos_of_lt (hU m hm).1 (hU m hm).2)).symm
  rw [MulChar.one_apply hpunit, MulChar.one_apply hnunit, MulChar.one_apply hmunit]
  simp

/-- Weighted nonprincipal kernel identity on a prime modulus. -/
theorem weightedNonprincipalKernelCollapse_prime
    {N : ℕ} (hN : N.Prime)
    {S T U : Finset ℕ}
    (hS : ∀ p ∈ S, 0 < p ∧ p < N)
    (hT : ∀ n ∈ T, 0 < n ∧ n < N)
    (hU : ∀ m ∈ U, 0 < m ∧ m < N)
    (w : ℕ → ℕ → ℕ → ℂ) :
    (∑ p ∈ S, ∑ n ∈ T, ∑ m ∈ U,
      w p n m *
        (∑ χ in nonprincipalCharacters N,
          χ (p : ZMod N) * χ (n : ZMod N) * star (χ (m : ZMod N)))) =
      ∑ p ∈ S, ∑ n ∈ T, ∑ m ∈ U,
        w p n m *
          ((if p * n ≡ m [MOD N] then (((N - 1 : ℕ) : ℂ)) else 0) - 1) := by
  classical
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  rw [charOrthMulKernel_prime_nonprincipal
    (N := N) (p := p) (n := n) (m := m) hN
    (hS p hp).1 (hS p hp).2
    (hT n hn).1 (hT n hn).2
    (hU m hm).1 (hU m hm).2]

end
end Dirichlet
end AnalyticNumberTheory
