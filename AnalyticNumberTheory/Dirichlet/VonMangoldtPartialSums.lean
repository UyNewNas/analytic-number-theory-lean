import AnalyticNumberTheory.Dirichlet.VonMangoldtWindow
import Mathlib.Tactic

open scoped BigOperators ArithmeticFunction
open Classical

namespace AnalyticNumberTheory
namespace Dirichlet

noncomputable section

/-- The cumulative character-twisted von-Mangoldt sum on `(0, X]`.

This is the standard finite summatory object targeted by Perron / explicit-formula
arguments.  Keeping it separate from the dyadic window lets downstream arguments prove a
prefix estimate first and recover `(P, 2P]` by subtraction. -/
def vonMangoldtCharacterPartialSum
    (N X : ℕ) (χ : DirichletCharacter ℂ N) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 X,
    ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)

/-- The dyadic von-Mangoldt character sum is exactly the difference of two cumulative sums.
This is a deterministic bridge only; it does not assert any Perron formula or quantitative
estimate for either side. -/
theorem dyadicVonMangoldtCharacterSum_eq_partial_sub_partial
    (N P : ℕ) (χ : DirichletCharacter ℂ N) :
    dyadicVonMangoldtCharacterSum N P χ =
      vonMangoldtCharacterPartialSum N (2 * P) χ -
        vonMangoldtCharacterPartialSum N P χ := by
  unfold dyadicVonMangoldtCharacterSum vonMangoldtCharacterPartialSum
  let f : ℕ → ℂ := fun n => ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)
  have hdisj : Disjoint (Finset.Ioc 0 P) (Finset.Ioc P (2 * P)) := by
    rw [Finset.disjoint_left]
    intro n hn0 hn1
    simp only [Finset.mem_Ioc] at hn0 hn1
    omega
  have hunion :
      Finset.Ioc 0 P ∪ Finset.Ioc P (2 * P) = Finset.Ioc 0 (2 * P) := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Ioc]
    omega
  have hsum :
      (∑ n ∈ Finset.Ioc 0 P, f n) +
          ∑ n ∈ Finset.Ioc P (2 * P), f n =
        ∑ n ∈ Finset.Ioc 0 (2 * P), f n := by
    rw [← hunion, Finset.sum_union hdisj]
  change (∑ n ∈ Finset.Ioc P (2 * P), f n) =
    (∑ n ∈ Finset.Ioc 0 (2 * P), f n) - ∑ n ∈ Finset.Ioc 0 P, f n
  rw [← hsum]
  ring

/-- Any quantitative estimate for the cumulative twisted von-Mangoldt sum transfers to the
dyadic interval with only the triangle-inequality loss at the two endpoints.  This packages
the exact consumer boundary expected from a future Perron / explicit-formula estimate. -/
theorem norm_dyadicVonMangoldtCharacterSum_le_partial_add_partial
    (N P : ℕ) (χ : DirichletCharacter ℂ N) :
    ‖dyadicVonMangoldtCharacterSum N P χ‖ ≤
      ‖vonMangoldtCharacterPartialSum N (2 * P) χ‖ +
        ‖vonMangoldtCharacterPartialSum N P χ‖ := by
  rw [dyadicVonMangoldtCharacterSum_eq_partial_sub_partial]
  exact norm_sub_le _ _

end

end Dirichlet
end AnalyticNumberTheory
