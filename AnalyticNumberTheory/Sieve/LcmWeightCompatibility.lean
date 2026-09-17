/-
! # Compatibility audit for the neutral LCM-weight helper layer

This module checks, in Lean, that the neutral `LcmWeightBounds` declarations can
serve as drop-in proof bodies for all four V1 helper signatures and all four V3
compatibility signatures.  It deliberately leaves the existing public
`PanV1SquareMean` / `PanV3SquareMean` declarations untouched; after this module is
machine-verified, those declarations can be converted to thin wrappers without
changing their statements or consumers.
-/

import AnalyticNumberTheory.Sieve.LcmWeightDivisorBounds
import AnalyticNumberTheory.Sieve.PanV1SquareMean
import AnalyticNumberTheory.Sieve.PanV3SquareMean

namespace AnalyticNumberTheory.Sieve.LcmWeightCompatibility

open Finset Real

noncomputable section

/-- Candidate body for the existing V1 `harmonic_Icc_le` signature. -/
theorem v1_harmonic_Icc_le (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ)) ≤ 1 + Real.log (M + 1) :=
  LcmWeightBounds.harmonic_Icc_le M

/-- Candidate body for the existing V1 `card_multiples_Icc` signature. -/
theorem v1_card_multiples_Icc (N m : ℕ) (hm : 1 ≤ m) :
    ((Finset.Icc 1 N).filter (fun n => m ∣ n)).card = N / m :=
  LcmWeightBounds.card_multiples_Icc N m hm

/-- Candidate body for the existing V1 `lcm_inv_sum_le` signature. -/
theorem v1_lcm_inv_sum_le (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
      (1 : ℝ) / (Nat.lcm d e : ℝ)) ≤
      (1 + Real.log (N + 1)) ^ 3 :=
  LcmWeightBounds.lcm_inv_sum_le N

/-- Candidate body for the existing V1 `divisorCountSq_sum_le` signature. -/
theorem v1_divisorCountSq_sum_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ 2)) ≤
      (N : ℝ) * (1 + Real.log (N + 1)) ^ 3 :=
  LcmWeightBounds.divisorCountSq_sum_le N

/-- Candidate body for the existing V3 `v3_harmonic_Icc_le` signature. -/
theorem v3_harmonic_Icc_le (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ)) ≤ 1 + Real.log (M + 1) :=
  LcmWeightBounds.harmonic_Icc_le M

/-- Candidate body for the existing V3 `v3_card_multiples_Icc` signature. -/
theorem v3_card_multiples_Icc (N m : ℕ) (hm : 1 ≤ m) :
    ((Finset.Icc 1 N).filter (fun n => m ∣ n)).card = N / m :=
  LcmWeightBounds.card_multiples_Icc N m hm

/-- Candidate body for the existing V3 `v3_lcm_inv_sum_le` signature. -/
theorem v3_lcm_inv_sum_le (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
      (1 : ℝ) / (Nat.lcm d e : ℝ)) ≤
      (1 + Real.log (N + 1)) ^ 3 :=
  LcmWeightBounds.lcm_inv_sum_le N

/-- Candidate body for the existing V3 `v3_divisorCountSq_sum_le` signature. -/
theorem v3_divisorCountSq_sum_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ 2)) ≤
      (N : ℝ) * (1 + Real.log (N + 1)) ^ 3 :=
  LcmWeightBounds.divisorCountSq_sum_le N

end

end AnalyticNumberTheory.Sieve.LcmWeightCompatibility
