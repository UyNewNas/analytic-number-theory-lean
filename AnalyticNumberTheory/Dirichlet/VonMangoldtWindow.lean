import AnalyticNumberTheory.Dirichlet.PrimeWindowWeights
import AnalyticNumberTheory.Dirichlet.VonMangoldtLSeries
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

open scoped BigOperators ArithmeticFunction
open Classical

namespace AnalyticNumberTheory
namespace Dirichlet

noncomputable section

open AnalyticNumberTheory.PrimeDistribution

/-- The finite von-Mangoldt weighted character sum over the dyadic interval `(P, 2P]`.
This is the finite object naturally produced by a truncated explicit formula before
prime powers are removed. -/
def dyadicVonMangoldtCharacterSum
    (N P : ℕ) (χ : DirichletCharacter ℂ N) : ℂ :=
  ∑ n ∈ Finset.Ioc P (2 * P),
    ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)

/-- The part of the dyadic von-Mangoldt character sum supported away from primes.
Only higher prime powers contribute numerically, since `Λ n = 0` off prime powers. -/
def dyadicVonMangoldtNonprimeRemainder
    (N P : ℕ) (χ : DirichletCharacter ℂ N) : ℂ :=
  ∑ n ∈ (Finset.Ioc P (2 * P)).filter (fun n => ¬ n.Prime),
    ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)

/-- Exact finite separation of the von-Mangoldt dyadic character sum into its prime
log-weighted part and the non-prime remainder.  This is the reusable finite bridge
between an explicit-formula estimate and `dyadicPrimeLogCharacterSum`. -/
theorem dyadicVonMangoldtCharacterSum_eq_primeLog_add_nonprime
    (N P : ℕ) (χ : DirichletCharacter ℂ N) :
    dyadicVonMangoldtCharacterSum N P χ =
      dyadicPrimeLogCharacterSum N P χ +
        dyadicVonMangoldtNonprimeRemainder N P χ := by
  unfold dyadicVonMangoldtCharacterSum dyadicVonMangoldtNonprimeRemainder
    dyadicPrimeLogCharacterSum weightedCharacterSumOn dyadicPrimeWindow
  calc
    (∑ n ∈ Finset.Ioc P (2 * P),
      ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)) =
        (∑ n ∈ (Finset.Ioc P (2 * P)).filter Nat.Prime,
          ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)) +
        ∑ n ∈ (Finset.Ioc P (2 * P)).filter (fun n => ¬ n.Prime),
          ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) := by
            exact (Finset.sum_filter_add_sum_filter_not
              (Finset.Ioc P (2 * P)) Nat.Prime
              (fun n => ((Λ n : ℝ) : ℂ) * χ (n : ZMod N))).symm
    _ = (∑ p ∈ (Finset.Ioc P (2 * P)).filter Nat.Prime,
          (Real.log (p : ℝ) : ℂ) * χ (p : ZMod N)) +
        ∑ n ∈ (Finset.Ioc P (2 * P)).filter (fun n => ¬ n.Prime),
          ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) := by
            congr 1
            apply Finset.sum_congr rfl
            intro p hp
            have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
            rw [ArithmeticFunction.vonMangoldt_apply_prime hpprime]

/-- A coefficient-free norm bound for the non-prime remainder.  The character contributes
at most one in norm, so the entire loss is the scalar von-Mangoldt mass of the non-prime
part of the dyadic interval. -/
theorem norm_dyadicVonMangoldtNonprimeRemainder_le
    {N P : ℕ} (χ : DirichletCharacter ℂ N) :
    ‖dyadicVonMangoldtNonprimeRemainder N P χ‖ ≤
      ∑ n ∈ (Finset.Ioc P (2 * P)).filter (fun n => ¬ n.Prime), Λ n := by
  unfold dyadicVonMangoldtNonprimeRemainder
  calc
    ‖∑ n ∈ (Finset.Ioc P (2 * P)).filter (fun n => ¬ n.Prime),
        ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)‖ ≤
      ∑ n ∈ (Finset.Ioc P (2 * P)).filter (fun n => ¬ n.Prime),
        ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod N)‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ n ∈ (Finset.Ioc P (2 * P)).filter (fun n => ¬ n.Prime), Λ n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have hχ := χ.norm_le_one (n : ZMod N)
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      nlinarith

end

end Dirichlet
end AnalyticNumberTheory
