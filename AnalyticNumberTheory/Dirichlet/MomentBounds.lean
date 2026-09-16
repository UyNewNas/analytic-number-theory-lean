import AnalyticNumberTheory.Dirichlet.Moments
import Mathlib.Tactic

open scoped BigOperators
open Classical

namespace AnalyticNumberTheory
namespace Dirichlet

noncomputable section

/-- Real norm-square form of the exact nonprincipal weighted second moment at a prime modulus.

This is the reusable estimate-facing version of
`weightedCharacterSumOn_nonprincipal_secondMoment_prime`: it removes the complex conjugation
bookkeeping and exposes the nonprincipal `L²` mass as an identity of nonnegative real quantities.
-/
theorem weightedCharacterSumOn_nonprincipal_normSq_prime
    {N : ℕ} (hN : N.Prime) {A : Finset ℕ}
    (hA : ∀ a ∈ A, 0 < a ∧ a < N) (w : ℕ → ℂ) :
    (∑ χ ∈ nonprincipalCharacters N,
      ‖weightedCharacterSumOn N A w χ‖ ^ 2) =
      (∑ a ∈ A, ‖w a‖ ^ 2) * (((N - 1 : ℕ) : ℝ)) -
        ‖∑ a ∈ A, w a‖ ^ 2 := by
  have h := weightedCharacterSumOn_nonprincipal_secondMoment_prime hN hA w
  change
    (∑ χ ∈ nonprincipalCharacters N,
      weightedCharacterSumOn N A w χ *
        (starRingEnd ℂ) (weightedCharacterSumOn N A w χ)) =
      (∑ a ∈ A, w a * (starRingEnd ℂ) (w a)) * (((N - 1 : ℕ) : ℂ)) -
        (∑ a ∈ A, w a) * (starRingEnd ℂ) (∑ a ∈ A, w a) at h
  have hmul (z : ℂ) :
      z * (starRingEnd ℂ) z = (((‖z‖ ^ 2 : ℝ) : ℂ)) := by
    have hz := Complex.mul_conj z
    rw [Complex.normSq_eq_norm_sq] at hz
    exact hz
  simp_rw [hmul] at h
  norm_cast at h

end
end Dirichlet
end AnalyticNumberTheory
