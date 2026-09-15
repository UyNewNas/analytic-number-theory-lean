import PrimeNumberTheoremAnd.Consequences
import PrimeNumberTheoremAnd.MediumPNT

/-!
# Prime-distribution API

This module is the stable facade over the ported PNTAnd implementation.
-/

namespace AnalyticNumberTheory.PrimeDistribution

open Asymptotics Filter Real
open MeasureTheory intervalIntegral
open scoped Chebyshev

/-- The genuine logarithmic integral used as the prime-distribution main term.

This is deliberately not the first asymptotic approximation `x / log x`.
The endpoint convention is `primeLogIntegral 2 = 0`, matching the interval
integral already used by PNTAnd's `pi_asymp` development. -/
noncomputable def primeLogIntegral (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, 1 / log t

/-- The chosen endpoint convention: the genuine logarithmic integral vanishes at `2`. -/
@[simp] theorem primeLogIntegral_two : primeLogIntegral 2 = 0 := by
  simp [primeLogIntegral]

/-- Adding a normalization constant changes only that constant.

This is the neutral ANT analogue of the normalization identity used by the
downstream Liu logarithmic-integral formalization at
`subfish-zhou/goldbach-lean@df1f3b3`, without importing its application-specific
weight layer. -/
@[simp] theorem primeLogIntegral_additive_normalization_sub (κ₂ κ₁ x : ℝ) :
    (κ₂ + primeLogIntegral x) - (κ₁ + primeLogIntegral x) = κ₂ - κ₁ := by
  ring

/-- The genuine logarithmic integral is nonnegative on its source range.

The proof is adapted from the corresponding downstream Liu logarithmic-integral
lemma at `subfish-zhou/goldbach-lean@df1f3b3`, using only neutral Mathlib
interval-integral facts. -/
theorem primeLogIntegral_nonneg {x : ℝ} (hx : 2 ≤ x) :
    0 ≤ primeLogIntegral x := by
  rw [primeLogIntegral]
  apply intervalIntegral.integral_nonneg hx
  intro t ht
  exact one_div_nonneg.mpr (le_of_lt (Real.log_pos (by linarith [ht.1])))

/-- Unfolding lemma for the stable genuine-`Li` API. -/
theorem primeLogIntegral_def (x : ℝ) :
    primeLogIntegral x = ∫ t in (2 : ℝ)..x, 1 / log t := rfl

/-- Exact Abel/partial-summation identity for prime counting, re-exported
from PNTAnd as the stable starting point for the quantitative `pi-Li` API. -/
theorem primeCounting_partialSummation (x : ℝ) (hx : 2 ≤ x) :
    Nat.primeCounting ⌊x⌋₊ =
      (log x)⁻¹ * Chebyshev.theta x +
        ∫ t in Set.Icc 2 x, Chebyshev.theta t * (t * log t ^ 2)⁻¹ :=
  pi_asymp_aux x hx

/-- Integration by parts for the genuine logarithmic integral.

This is the full source range `x ≥ 2`.  The proof uses the same underlying
`integral_log_inv` identity as the downstream Liu logarithmic-integral
formalization at `subfish-zhou/goldbach-lean@df1f3b3`; no application-specific
weight definitions are imported here. -/
theorem primeLogIntegral_eq_main_add_tail (x : ℝ) (hx : 2 ≤ x) :
    primeLogIntegral x = x / log x - 2 / log 2 +
      ∫ t in Set.Icc 2 x, 1 / (log t) ^ 2 := by
  rw [primeLogIntegral, intervalIntegral.integral_of_le hx,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have h := integral_log_inv 2 x (by norm_num) (by linarith)
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hx,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hx,
    ← mul_one_div, one_div, ← mul_one_div, one_div]
  simp only [one_div, h, mul_comm]

/-- Exact error decomposition for prime counting against the fixed normalized
logarithmic integral `2 / log 2 + primeLogIntegral x`.

This isolates the two quantities that a quantitative `pi-Li` theorem must pay:
the endpoint theta error and its partial-summation integral.  The downstream
`primeCount_li_pnt` theorem at `subfish-zhou/goldbach-lean@df1f3b3` obtains an
arbitrary logarithmic saving from the `q = 1` specialization of its proved
Standard Bombieri--Vinogradov theorem.  ANT keeps only this neutral identity
here; no downstream BV/application layer is imported. -/
theorem primeCounting_sub_normalizedLi_eq (x : ℝ) (hx : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) - (2 / log 2 + primeLogIntegral x) =
      ((log x)⁻¹ * Chebyshev.theta x - x / log x) +
        ((∫ t in Set.Icc 2 x, Chebyshev.theta t * (t * log t ^ 2)⁻¹) -
          ∫ t in Set.Icc 2 x, 1 / (log t) ^ 2) := by
  rw [primeCounting_partialSummation x hx, primeLogIntegral_eq_main_add_tail x hx]
  ring

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

/-- **π 上界 (ant #17, 里程碑 2)**: 由 PNT 取显式常数, 对 `x ≥ 2` 一致地
`π(x) ≤ C·x/log x`. 这是三因子主项估计中 `switchingCount ≤ π(N/a)` 的
解析上界 (`≤ C·N/(a·log(N/a))`). -/
theorem primeCounting_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 2 ≤ x →
      (Nat.primeCounting x : ℝ) ≤ C * (x : ℝ) / log (x : ℝ) := by
  obtain ⟨c, hc, hcount⟩ := natPrimeCountingPNT
  obtain ⟨C₀, hC₀ev⟩ := (hc.isBigO).bound
  rcases Filter.eventually_atTop.mp hC₀ev with ⟨X₀, hX₀⟩
  let C₀b : ℝ := max C₀ 1
  have hC0b : 1 ≤ C₀b := by
    dsimp [C₀b]
    exact le_max_right _ _
  let X : ℕ := max X₀ 2
  let C : ℝ := max (1 + C₀b) (2 * log (X : ℝ))
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    have h1 : 0 < 1 + C₀b := by linarith
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  · intro x hx
    by_cases hxbig : X ≤ x
    · have hx1 : (1 : ℝ) < x := by exact_mod_cast (by omega : 1 < x)
      have hlog : 0 < log (x : ℝ) := Real.log_pos hx1
      have hcx : |c x| ≤ C₀b := by
        have h0 : |c x| ≤ C₀ := by
          simpa using hX₀ x (le_trans (le_max_left X₀ 2) hxbig)
        exact le_trans h0 (le_max_left _ _)
      have hmain : (Nat.primeCounting x : ℝ) ≤ (1 + C₀b) * (x : ℝ) / log (x : ℝ) := by
        rw [hcount]
        have hle : 1 + c x ≤ 1 + C₀b := by linarith [le_trans (le_abs_self (c x)) hcx]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hle (by positivity : 0 ≤ (x : ℝ))) (le_of_lt hlog)
      have hC : (1 + C₀b) * (x : ℝ) / log (x : ℝ) ≤ C * (x : ℝ) / log (x : ℝ) := by
        have hC1 : 1 + C₀b ≤ C := by
          dsimp [C]
          exact le_max_left _ _
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC1 (by positivity : 0 ≤ (x : ℝ))) (le_of_lt hlog)
      exact le_trans hmain hC
    · have hxlt : x < X := lt_of_not_ge hxbig
      have hpi : (Nat.primeCounting x : ℝ) ≤ (x : ℝ) + 1 := by
        have hle : Nat.primeCounting x ≤ x + 1 := by
          change Nat.count Nat.Prime (x + 1) ≤ x + 1
          exact Nat.count_le Nat.Prime
        exact_mod_cast hle
      have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ x)
      have hlog : 0 < log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
      have hlogX : 0 < log (X : ℝ) := by
        have hX2 : (2 : ℝ) ≤ X := by exact_mod_cast (le_max_right X₀ 2)
        exact Real.log_pos (by linarith)
      have hlogx_le : log (x : ℝ) ≤ log (X : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast (le_of_lt hxlt))
      have hC2 : 2 * log (x : ℝ) ≤ C := by
        dsimp [C]
        calc
          2 * log (x : ℝ) ≤ 2 * log (X : ℝ) := by gcongr
          _ ≤ max (1 + C₀b) (2 * log (X : ℝ)) := le_max_right _ _
      calc
        (Nat.primeCounting x : ℝ) ≤ (x : ℝ) + 1 := hpi
        _ ≤ 2 * (x : ℝ) := by linarith
        _ = (2 * log (x : ℝ)) * (x : ℝ) / log (x : ℝ) := by
              field_simp [hlog.ne']
        _ ≤ C * (x : ℝ) / log (x : ℝ) := by
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right hC2 (by positivity : 0 ≤ (x : ℝ))) (le_of_lt hlog)

end AnalyticNumberTheory.PrimeDistribution
