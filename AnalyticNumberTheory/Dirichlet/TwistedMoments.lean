import AnalyticNumberTheory.Dirichlet.Moments
import Mathlib.Tactic

open scoped BigOperators
open Classical

namespace AnalyticNumberTheory
namespace Dirichlet

noncomputable section

/-- Twisted weighted Plancherel at a prime modulus.  Multiplication by the positive
representative `d` inserts one Dirichlet-character factor, and character orthogonality
turns the resulting second moment into the exact modular incidence relation
`d * a ≡ b (mod N)`.

This statement is coefficient-agnostic and finite; no analytic estimate or GRH input enters. -/
theorem weightedCharacterSumOn_twistedSecondMoment_prime
    {N d : ℕ} (hN : N.Prime) (hd0 : 0 < d) (hdN : d < N)
    {A B : Finset ℕ}
    (hA : ∀ a ∈ A, 0 < a ∧ a < N)
    (hB : ∀ b ∈ B, 0 < b ∧ b < N)
    (u v : ℕ → ℂ) :
    (∑ χ : DirichletCharacter ℂ N,
      χ (d : ZMod N) *
        weightedCharacterSumOn N A u χ *
          star (weightedCharacterSumOn N B v χ)) =
      ∑ a ∈ A, ∑ b ∈ B,
        (u a * star (v b)) *
          (if d * a ≡ b [MOD N] then (((N - 1 : ℕ) : ℂ)) else 0) := by
  classical
  calc
    (∑ χ : DirichletCharacter ℂ N,
      χ (d : ZMod N) *
        weightedCharacterSumOn N A u χ *
          star (weightedCharacterSumOn N B v χ)) =
        ∑ χ : DirichletCharacter ℂ N,
          ∑ a ∈ A, ∑ b ∈ B,
            χ (d : ZMod N) *
              (u a * χ (a : ZMod N)) *
                (star (v b) * star (χ (b : ZMod N))) := by
              apply Finset.sum_congr rfl
              intro χ _hχ
              simp [weightedCharacterSumOn, Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
    _ = ∑ a ∈ A, ∑ b ∈ B,
          ∑ χ : DirichletCharacter ℂ N,
            χ (d : ZMod N) *
              (u a * χ (a : ZMod N)) *
                (star (v b) * star (χ (b : ZMod N))) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro a _ha
              rw [Finset.sum_comm]
    _ = ∑ a ∈ A, ∑ b ∈ B,
          (u a * star (v b)) *
            (∑ χ : DirichletCharacter ℂ N,
              χ (d : ZMod N) * χ (a : ZMod N) * star (χ (b : ZMod N))) := by
              apply Finset.sum_congr rfl
              intro a _ha
              apply Finset.sum_congr rfl
              intro b _hb
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro χ _hχ
              ring
    _ = ∑ a ∈ A, ∑ b ∈ B,
          (u a * star (v b)) *
            (if d * a ≡ b [MOD N] then (((N - 1 : ℕ) : ℂ)) else 0) := by
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro b hb
              rw [charOrthMulKernel_prime hN hd0 hdN
                (hA a ha).1 (hA a ha).2
                (hB b hb).1 (hB b hb).2]

end
end Dirichlet
end AnalyticNumberTheory
