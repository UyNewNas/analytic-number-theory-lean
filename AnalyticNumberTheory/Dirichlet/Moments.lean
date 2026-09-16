import AnalyticNumberTheory.Dirichlet.Decomposition
import Mathlib.Tactic

open scoped BigOperators
open Classical

namespace AnalyticNumberTheory
namespace Dirichlet

noncomputable section

/-- Finite Dirichlet-character sum over a set of positive integer representatives. -/
def characterSumOn (N : ℕ) (A : Finset ℕ) (χ : DirichletCharacter ℂ N) : ℂ :=
  ∑ a ∈ A, χ (a : ZMod N)

/-- At a prime modulus, if every element of `A` is a nonzero representative below the modulus,
the principal character sum is exactly `A.card`. -/
theorem characterSumOn_principal_prime
    {N : ℕ} (hN : N.Prime) {A : Finset ℕ}
    (hA : ∀ a ∈ A, 0 < a ∧ a < N) :
    characterSumOn N A (1 : DirichletCharacter ℂ N) = (A.card : ℂ) := by
  classical
  unfold characterSumOn
  calc
    (∑ a ∈ A, (1 : DirichletCharacter ℂ N) (a : ZMod N)) =
        ∑ a ∈ A, (1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro a ha
          have haunit : IsUnit (a : ZMod N) := by
            rw [ZMod.isUnit_iff_coprime]
            exact ((Nat.Prime.coprime_iff_not_dvd hN).2
              (Nat.not_dvd_of_pos_of_lt (hA a ha).1 (hA a ha).2)).symm
          exact MulChar.one_apply haunit
    _ = (A.card : ℂ) := by simp

/-- Exact character second moment on any finite set of distinct positive representatives below a
prime modulus.  This is the finite Plancherel identity behind prime-window character moments. -/
theorem characterSumOn_secondMoment_prime
    {N : ℕ} (hN : N.Prime) {A : Finset ℕ}
    (hA : ∀ a ∈ A, 0 < a ∧ a < N) :
    (∑ χ : DirichletCharacter ℂ N,
      characterSumOn N A χ * star (characterSumOn N A χ)) =
      (A.card : ℂ) * (((N - 1 : ℕ) : ℂ)) := by
  classical
  calc
    (∑ χ : DirichletCharacter ℂ N,
      characterSumOn N A χ * star (characterSumOn N A χ)) =
        ∑ χ : DirichletCharacter ℂ N,
          ∑ a ∈ A, ∑ b ∈ A,
            χ (a : ZMod N) * star (χ (b : ZMod N)) := by
              apply Finset.sum_congr rfl
              intro χ _hχ
              simp [characterSumOn, Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
    _ = ∑ a ∈ A, ∑ b ∈ A,
          ∑ χ : DirichletCharacter ℂ N,
            χ (a : ZMod N) * star (χ (b : ZMod N)) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro a _ha
              rw [Finset.sum_comm]
    _ = ∑ a ∈ A, ∑ b ∈ A,
          if a = b then (((N - 1 : ℕ) : ℂ)) else 0 := by
            apply Finset.sum_congr rfl
            intro a ha
            apply Finset.sum_congr rfl
            intro b hb
            rw [charOrthKernel_prime_two hN
              (hA a ha).1 (hA a ha).2
              (hA b hb).1 (hA b hb).2]
    _ = ∑ a ∈ A, (((N - 1 : ℕ) : ℂ)) := by
          apply Finset.sum_congr rfl
          intro a ha
          simp [ha]
    _ = (A.card : ℂ) * (((N - 1 : ℕ) : ℂ)) := by simp

/-- Principal contribution to the exact second moment. -/
theorem characterSumOn_principal_secondMoment_prime
    {N : ℕ} (hN : N.Prime) {A : Finset ℕ}
    (hA : ∀ a ∈ A, 0 < a ∧ a < N) :
    characterSumOn N A (1 : DirichletCharacter ℂ N) *
        star (characterSumOn N A (1 : DirichletCharacter ℂ N)) =
      (A.card : ℂ) * (A.card : ℂ) := by
  rw [characterSumOn_principal_prime hN hA]
  simp

/-- Exact nonprincipal `L²` mass after subtracting the principal character. -/
theorem characterSumOn_nonprincipal_secondMoment_prime
    {N : ℕ} (hN : N.Prime) {A : Finset ℕ}
    (hA : ∀ a ∈ A, 0 < a ∧ a < N) :
    (∑ χ ∈ nonprincipalCharacters N,
      characterSumOn N A χ * star (characterSumOn N A χ)) =
      (A.card : ℂ) * (((N - 1 : ℕ) : ℂ)) -
        (A.card : ℂ) * (A.card : ℂ) := by
  let F : DirichletCharacter ℂ N → ℂ := fun χ =>
    characterSumOn N A χ * star (characterSumOn N A χ)
  have hsplit := sum_chars_eq_principal_add_nonprincipal (N := N) F
  have hrev :
      (∑ χ ∈ nonprincipalCharacters N, F χ) + F 1 =
        ∑ χ : DirichletCharacter ℂ N, F χ := by
    calc
      (∑ χ ∈ nonprincipalCharacters N, F χ) + F 1 =
          F 1 + ∑ χ ∈ nonprincipalCharacters N, F χ := by rw [add_comm]
      _ = ∑ χ : DirichletCharacter ℂ N, F χ := hsplit.symm
  have hnonprincipal := eq_sub_of_add_eq hrev
  rw [characterSumOn_secondMoment_prime hN hA,
    characterSumOn_principal_secondMoment_prime hN hA] at hnonprincipal
  exact hnonprincipal

end
end Dirichlet
end AnalyticNumberTheory
