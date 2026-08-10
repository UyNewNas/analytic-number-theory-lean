import PrimeNumberTheoremAnd.Consequences
import PrimeNumberTheoremAnd.MediumPNT

/-!
# Prime-distribution API

This module is the stable facade over the ported PNTAnd implementation.
-/

namespace AnalyticNumberTheory.PrimeDistribution

open Asymptotics Filter Real
open scoped Chebyshev

/-- A medium-strength prime number theorem for Chebyshev's psi function. -/
theorem chebyshevPsi_medium_error :
    ∃ c > 0,
      (Chebyshev.psi - id) =O[atTop]
        fun x : ℝ => x * exp (-c * log x ^ ((1 : ℝ) / 10)) :=
  MediumPNT

/-- The prime-counting PNT in the real-variable normal form proved by PNTAnd. -/
theorem primeCounting_asymptotic_real :
    ∃ c : ℝ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ x : ℝ,
        Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x :=
  pi_alt

/-- A natural-number interface for the prime-counting PNT. -/
def NatPrimeCountingPNT : Prop :=
  ∃ c : ℕ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
    ∀ x : ℕ,
      (Nat.primeCounting x : ℝ) = (1 + c x) * (x : ℝ) / log x

/-- Restrict the real-variable prime-counting PNT to natural arguments. -/
theorem natPrimeCountingPNT : NatPrimeCountingPNT := by
  obtain ⟨c, hc, hcount⟩ := primeCounting_asymptotic_real
  refine ⟨fun n => c n, hc.comp_tendsto tendsto_natCast_atTop_atTop, ?_⟩
  intro n
  simpa using hcount (n : ℝ)

end AnalyticNumberTheory.PrimeDistribution
