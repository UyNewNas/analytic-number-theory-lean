import AnalyticNumberTheory.Mertens.PartialSummation

/-!
# Finite logarithmic bridge for Mertens' product theorem

This module isolates the elementary part of the product argument.  The
identification of the limiting constant with Euler's constant is deliberately
kept separate: it requires an Euler-product/Abelian bridge, rather than only
the prime-number theorem.
-/

namespace AnalyticNumberTheory.Mertens

open Finset Real

/-- The finite quadratic-and-higher correction in the logarithm of the prime
Euler product. -/
noncomputable def logarithmicCorrection (x : ℕ) : ℝ :=
  (primesUpTo x).sum fun p => -log (1 - 1 / (p : ℝ)) - 1 / (p : ℝ)

/-- Taking the logarithm of the finite Euler product separates the reciprocal
prime sum from its convergent higher-order correction. -/
theorem neg_log_primeProduct_eq_reciprocal_add_correction (x : ℕ) :
    -log (primeProduct x) = primeReciprocalSum x + logarithmicCorrection x := by
  rw [log_primeProduct]
  unfold primeReciprocalSum logarithmicCorrection
  rw [← Finset.sum_neg_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

end AnalyticNumberTheory.Mertens
