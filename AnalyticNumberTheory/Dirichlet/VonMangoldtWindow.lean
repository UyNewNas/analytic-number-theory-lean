import AnalyticNumberTheory.Dirichlet.PrimeWindowWeights
import AnalyticNumberTheory.Dirichlet.VonMangoldtLSeries
import Mathlib.NumberTheory.Chebyshev
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

/-- The scalar mass of higher prime powers in a dyadic interval has the standard explicit
Chebyshev bound `O(sqrt(P) log P)`.  This packages mathlib's `ψ - θ` estimate in exactly
the finite interval shape needed for character sums. -/
theorem dyadicVonMangoldtNonprimeMass_le
    {P : ℕ} (hP : 0 < P) :
    (∑ n ∈ (Finset.Ioc P (2 * P)).filter (fun n => ¬ n.Prime), Λ n) ≤
      2 * Real.sqrt (((2 * P : ℕ) : ℝ)) * Real.log (((2 * P : ℕ) : ℝ)) := by
  let A := (Finset.Ioc P (2 * P)).filter (fun n => ¬ n.Prime)
  let B := (Finset.Ioc 0 (2 * P)).filter (fun n => ¬ n.Prime)
  have hAB : A ⊆ B := by
    intro n hn
    simp only [A, B, Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    exact ⟨⟨by omega, hn.1.2⟩, hn.2⟩
  have hsum : (∑ n ∈ A, Λ n) ≤ ∑ n ∈ B, Λ n := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hAB
      (fun n _hn _hnot => ArithmeticFunction.vonMangoldt_nonneg)
  have hB :
      (∑ n ∈ B, Λ n) =
        Chebyshev.psi (((2 * P : ℕ) : ℝ)) -
          Chebyshev.theta (((2 * P : ℕ) : ℝ)) := by
    symm
    simpa only [B, Nat.floor_natCast] using
      (Chebyshev.psi_sub_theta_eq_sum_not_prime (((2 * P : ℕ) : ℝ)))
  have hx : (1 : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * P by omega)
  have hcheb := Chebyshev.psi_sub_theta_le (x := (((2 * P : ℕ) : ℝ))) hx
  change (∑ n ∈ A, Λ n) ≤ _
  calc
    (∑ n ∈ A, Λ n) ≤ ∑ n ∈ B, Λ n := hsum
    _ = Chebyshev.psi (((2 * P : ℕ) : ℝ)) -
          Chebyshev.theta (((2 * P : ℕ) : ℝ)) := hB
    _ ≤ 2 * Real.sqrt (((2 * P : ℕ) : ℝ)) * Real.log (((2 * P : ℕ) : ℝ)) := hcheb

/-- Uniform prime-power removal for a Dirichlet-character twist: the non-prime part costs at
most the same explicit `O(sqrt(P) log P)` Chebyshev term. -/
theorem norm_dyadicVonMangoldtNonprimeRemainder_le_sqrtLog
    {N P : ℕ} (χ : DirichletCharacter ℂ N) (hP : 0 < P) :
    ‖dyadicVonMangoldtNonprimeRemainder N P χ‖ ≤
      2 * Real.sqrt (((2 * P : ℕ) : ℝ)) * Real.log (((2 * P : ℕ) : ℝ)) :=
  le_trans (norm_dyadicVonMangoldtNonprimeRemainder_le χ)
    (dyadicVonMangoldtNonprimeMass_le hP)

/-- Removing higher prime powers from a dyadic von-Mangoldt character sum loses only the
explicit Chebyshev `O(sqrt(P) log P)` term.  Thus a future GRH bound for the total
von-Mangoldt sum transfers directly to the log-weighted prime sum. -/
theorem norm_dyadicPrimeLogCharacterSum_le_vonMangoldt_add_sqrtLog
    {N P : ℕ} (χ : DirichletCharacter ℂ N) (hP : 0 < P) :
    ‖dyadicPrimeLogCharacterSum N P χ‖ ≤
      ‖dyadicVonMangoldtCharacterSum N P χ‖ +
        2 * Real.sqrt (((2 * P : ℕ) : ℝ)) * Real.log (((2 * P : ℕ) : ℝ)) := by
  have hsplit := dyadicVonMangoldtCharacterSum_eq_primeLog_add_nonprime N P χ
  have hrearr :
      dyadicPrimeLogCharacterSum N P χ =
        dyadicVonMangoldtCharacterSum N P χ -
          dyadicVonMangoldtNonprimeRemainder N P χ := by
    rw [hsplit]
    ring
  rw [hrearr]
  exact le_trans (norm_sub_le _ _)
    (add_le_add le_rfl (norm_dyadicVonMangoldtNonprimeRemainder_le_sqrtLog χ hP))

/-- Complete deterministic reduction from the unweighted dyadic prime-character sum to the
finite von-Mangoldt character sum.  The two explicit losses are exactly the higher-prime-power
Chebyshev term and the `log p - log P` dyadic weight-removal term. -/
theorem norm_characterSumOn_dyadicPrimeWindow_le_vonMangoldt
    {N P : ℕ} (χ : DirichletCharacter ℂ N) (hP : 1 < P) :
    ‖characterSumOn N (dyadicPrimeWindow P) χ‖ ≤
      (‖dyadicVonMangoldtCharacterSum N P χ‖ +
          2 * Real.sqrt (((2 * P : ℕ) : ℝ)) * Real.log (((2 * P : ℕ) : ℝ)) +
          Real.log 2 * ((dyadicPrimeWindow P).card : ℝ)) /
        Real.log (P : ℝ) := by
  have hprime :=
    norm_dyadicPrimeLogCharacterSum_le_vonMangoldt_add_sqrtLog
      χ (Nat.zero_lt_of_lt hP)
  have hremove := norm_characterSumOn_dyadicPrimeWindow_le_div_log χ hP
  have hnum :
      ‖dyadicPrimeLogCharacterSum N P χ‖ +
          Real.log 2 * ((dyadicPrimeWindow P).card : ℝ) ≤
        (‖dyadicVonMangoldtCharacterSum N P χ‖ +
          2 * Real.sqrt (((2 * P : ℕ) : ℝ)) * Real.log (((2 * P : ℕ) : ℝ))) +
          Real.log 2 * ((dyadicPrimeWindow P).card : ℝ) :=
    add_le_add_right hprime _
  have hlog : 0 ≤ Real.log (P : ℝ) :=
    (Real.log_pos (by exact_mod_cast hP)).le
  exact hremove.trans (div_le_div_of_nonneg_right hnum hlog)

end

end Dirichlet
end AnalyticNumberTheory
