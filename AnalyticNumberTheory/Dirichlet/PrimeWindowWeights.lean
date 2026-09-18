import AnalyticNumberTheory.Dirichlet.Moments
import AnalyticNumberTheory.PrimeDistribution.DyadicPrimeWindow
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic

open scoped BigOperators
open Classical

namespace AnalyticNumberTheory
namespace Dirichlet

noncomputable section

open AnalyticNumberTheory.PrimeDistribution

/-- Log-weighted Dirichlet character sum over the dyadic prime window `(P, 2P]`. -/
def dyadicPrimeLogCharacterSum (N P : ℕ) (χ : DirichletCharacter ℂ N) : ℂ :=
  weightedCharacterSumOn N (dyadicPrimeWindow P)
    (fun p => (Real.log (p : ℝ) : ℂ)) χ

/-- The finite remainder left after replacing `log p` by the constant `log P`
on a dyadic prime window. -/
def dyadicPrimeLogRemainder (N P : ℕ) (χ : DirichletCharacter ℂ N) : ℂ :=
  weightedCharacterSumOn N (dyadicPrimeWindow P)
    (fun p => (Real.log (p : ℝ) : ℂ) - (Real.log (P : ℝ) : ℂ)) χ

/-- On `(P,2P]`, the logarithmic weight differs from `log P` by a nonnegative amount. -/
theorem dyadicPrime_log_sub_log_nonneg
    {P p : ℕ} (hP : 0 < P) (hp : p ∈ dyadicPrimeWindow P) :
    0 ≤ Real.log (p : ℝ) - Real.log (P : ℝ) := by
  have hmem := (mem_dyadicPrimeWindow (P := P) (p := p)).1 hp
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hPp : (P : ℝ) ≤ p := by exact_mod_cast (Nat.le_of_lt hmem.1)
  have hlog : Real.log (P : ℝ) ≤ Real.log (p : ℝ) := Real.log_le_log hP0 hPp
  linarith

/-- On `(P,2P]`, the logarithmic weight differs from `log P` by at most `log 2`. -/
theorem dyadicPrime_log_sub_log_le_log_two
    {P p : ℕ} (hP : 0 < P) (hp : p ∈ dyadicPrimeWindow P) :
    Real.log (p : ℝ) - Real.log (P : ℝ) ≤ Real.log 2 := by
  have hmem := (mem_dyadicPrimeWindow (P := P) (p := p)).1 hp
  have hp0nat : 0 < p := lt_of_lt_of_le hP hmem.1.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp0nat
  have hp2P : (p : ℝ) ≤ ((2 * P : ℕ) : ℝ) := by exact_mod_cast hmem.2.1
  have hlogp : Real.log (p : ℝ) ≤ Real.log ((2 * P : ℕ) : ℝ) :=
    Real.log_le_log hp0 hp2P
  have hlog2P :
      Real.log ((2 * P : ℕ) : ℝ) = Real.log 2 + Real.log (P : ℝ) := by
    norm_num [Nat.cast_mul]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (P : ℝ) ≠ 0)]
  rw [hlog2P] at hlogp
  linarith

/-- Exact finite decomposition of a log-weighted prime character sum into the constant
`log P` times the unweighted character sum plus a short logarithmic remainder. -/
theorem dyadicPrimeLogCharacterSum_eq_log_mul_add_remainder
    (N P : ℕ) (χ : DirichletCharacter ℂ N) :
    dyadicPrimeLogCharacterSum N P χ =
      (Real.log (P : ℝ) : ℂ) * characterSumOn N (dyadicPrimeWindow P) χ +
        dyadicPrimeLogRemainder N P χ := by
  unfold dyadicPrimeLogCharacterSum dyadicPrimeLogRemainder
  simp only [weightedCharacterSumOn, characterSumOn]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Trivial but useful dyadic control of the logarithmic remainder: its norm is at most
`log 2` times the number of primes in the window. -/
theorem norm_dyadicPrimeLogRemainder_le
    {N P : ℕ} (χ : DirichletCharacter ℂ N) (hP : 0 < P) :
    ‖dyadicPrimeLogRemainder N P χ‖ ≤
      Real.log 2 * ((dyadicPrimeWindow P).card : ℝ) := by
  unfold dyadicPrimeLogRemainder weightedCharacterSumOn
  calc
    ‖∑ p ∈ dyadicPrimeWindow P,
        ((Real.log (p : ℝ) : ℂ) - (Real.log (P : ℝ) : ℂ)) * χ (p : ZMod N)‖
        ≤ ∑ p ∈ dyadicPrimeWindow P,
            ‖((Real.log (p : ℝ) : ℂ) - (Real.log (P : ℝ) : ℂ)) *
              χ (p : ZMod N)‖ :=
      norm_sum_le (dyadicPrimeWindow P)
        (fun p => ((Real.log (p : ℝ) : ℂ) - (Real.log (P : ℝ) : ℂ)) * χ (p : ZMod N))
    _ ≤ ∑ p ∈ dyadicPrimeWindow P, Real.log 2 := by
      apply Finset.sum_le_sum
      intro p hp
      have hnonneg := dyadicPrime_log_sub_log_nonneg hP hp
      have hupper := dyadicPrime_log_sub_log_le_log_two hP hp
      have hcoeff :
          ‖(Real.log (p : ℝ) : ℂ) - (Real.log (P : ℝ) : ℂ)‖ =
            Real.log (p : ℝ) - Real.log (P : ℝ) := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      rw [norm_mul, hcoeff]
      have hχ := χ.norm_le_one (p : ZMod N)
      have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
      nlinarith
    _ = Real.log 2 * ((dyadicPrimeWindow P).card : ℝ) := by
      simp [mul_comm]

/-- Removing the logarithmic weight costs only the explicit `log 2` window term.
This is the finite bridge used before applying a von-Mangoldt/explicit-formula estimate. -/
theorem log_mul_norm_characterSumOn_dyadicPrimeWindow_le
    {N P : ℕ} (χ : DirichletCharacter ℂ N) (hP : 1 < P) :
    Real.log (P : ℝ) * ‖characterSumOn N (dyadicPrimeWindow P) χ‖ ≤
      ‖dyadicPrimeLogCharacterSum N P χ‖ +
        Real.log 2 * ((dyadicPrimeWindow P).card : ℝ) := by
  have hP0 : 0 < P := Nat.zero_lt_of_lt hP
  have hlogP : 0 < Real.log (P : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hP)
  have hid := dyadicPrimeLogCharacterSum_eq_log_mul_add_remainder N P χ
  have hrearr :
      (Real.log (P : ℝ) : ℂ) * characterSumOn N (dyadicPrimeWindow P) χ =
        dyadicPrimeLogCharacterSum N P χ - dyadicPrimeLogRemainder N P χ := by
    rw [hid]
    ring
  calc
    Real.log (P : ℝ) * ‖characterSumOn N (dyadicPrimeWindow P) χ‖ =
        ‖(Real.log (P : ℝ) : ℂ) * characterSumOn N (dyadicPrimeWindow P) χ‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogP]
    _ = ‖dyadicPrimeLogCharacterSum N P χ - dyadicPrimeLogRemainder N P χ‖ := by
          rw [hrearr]
    _ ≤ ‖dyadicPrimeLogCharacterSum N P χ‖ + ‖dyadicPrimeLogRemainder N P χ‖ :=
          norm_sub_le _ _
    _ ≤ ‖dyadicPrimeLogCharacterSum N P χ‖ +
          Real.log 2 * ((dyadicPrimeWindow P).card : ℝ) := by
          gcongr
          exact norm_dyadicPrimeLogRemainder_le χ hP0

/-- Divided form of `log_mul_norm_characterSumOn_dyadicPrimeWindow_le`, exposing the familiar
`1 / log P` loss when passing from a log-weighted prime sum to the unweighted prime sum. -/
theorem norm_characterSumOn_dyadicPrimeWindow_le_div_log
    {N P : ℕ} (χ : DirichletCharacter ℂ N) (hP : 1 < P) :
    ‖characterSumOn N (dyadicPrimeWindow P) χ‖ ≤
      (‖dyadicPrimeLogCharacterSum N P χ‖ +
        Real.log 2 * ((dyadicPrimeWindow P).card : ℝ)) / Real.log (P : ℝ) := by
  have hlogP : 0 < Real.log (P : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hP)
  rw [le_div_iff₀ hlogP]
  simpa [mul_comm] using log_mul_norm_characterSumOn_dyadicPrimeWindow_le χ hP

end

end Dirichlet
end AnalyticNumberTheory
