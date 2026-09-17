/-
Copyright (c) 2026 UyNewNas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Source/API audit:
* Pinned mathlib
  @ e4c91783ca8e6a7c693ae624ade32fd22d4e43c1,
  `Mathlib/Analysis/Complex/JensenFormula.lean`, declaration
  `AnalyticOnNhd.sum_divisor_le`.  This is already a quantitative Jensen
  inequality, stated canonically with the analytic divisor and multiplicity.
* AlexKontorovich/PrimeNumberTheoremAnd
  @ a5154676af9aa3095150ee410cdda80555aa0642,
  `PrimeNumberTheoremAnd/StrongPNT.lean`, declaration `ZerosBound`.
* AxiomMath/PrimeNumberTheoremAnd
  @ 75c7dffd3ddfe2bda7c33264c780a97486f8303d retains the same `ZerosBound` API.
* anthropics/formal-math
  @ fbdc36bbf17d20af3fd0447c6d1a8a02773c9844 consumes the PNT+ Jensen bound
  in the Dirichlet-character local-zero-count route.
* Canonical same-revision `subfish-zhou/goldbach-lean`
  @ 09b97db5764ade1246bfb77206baa1b124760958 has no competing packaged
  analytic-order/divisor zero-multiplicity adapter.

The pinned mathlib theorem is stronger and more canonical than copying the
upstream Blaschke/Borel--Caratheodory implementation.  This module therefore
adds only normalized-origin thin adapters; it does not duplicate Jensen's
formula or the upstream `ZerosBound` proof.
-/

import AnalyticNumberTheory.ComplexAnalysis.JensenZeros
import Mathlib.Analysis.Complex.JensenFormula

namespace AnalyticNumberTheory.ComplexAnalysis

/-- Quantitative Jensen zero-multiplicity bound at the origin, specialized to
`f 0 = 1`.

This is a thin adapter around pinned mathlib's
`AnalyticOnNhd.sum_divisor_le`.  We deliberately retain mathlib's canonical
`|r|` in the divisor support; downstream positive-radius callers may simplify
it with `abs_of_pos` at their application boundary. -/
theorem jensenDivisorBound_normalized {B r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (one_le_B : 1 ≤ B)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    (hf0_eq_one : f 0 = 1)
    (fz_bound : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∑ᶠ u, MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) |r|) u ≤
      Real.log B / Real.log (R / r) := by
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  have h := AnalyticOnNhd.sum_divisor_le
    (c := (0 : ℂ)) (r := r) (R := R) (M := B)
    (by simpa [abs_of_pos r_pos] using r_pos)
    (by simpa [abs_of_pos r_pos, abs_of_pos R_pos] using r_lt_R)
    one_le_B
    (by simpa [abs_of_pos R_pos] using hfAnalytic)
    (by rw [hf0_eq_one]; exact one_ne_zero)
    (by simpa [abs_of_pos R_pos] using fz_bound)
  simpa [hf0_eq_one] using h

/-- Convert the normalized Jensen divisor bound to the corresponding sum of
actual analytic zero multiplicities in the inner closed disc.

The only extra work beyond `jensenDivisorBound_normalized` is bookkeeping:
the analytic divisor has support only at zeros, and on the connected outer
disc its value at a zero is exactly `analyticOrderNatAt`.  The normalization
`f 0 = 1` rules out an identically-zero component, so all these orders are
finite.  This is the neutral seam used by Dirichlet-L local zero counts. -/
theorem jensenZeroMultiplicityBound_normalized {B r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (one_le_B : 1 ≤ B)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    (hf0_eq_one : f 0 = 1)
    (fz_bound : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ B) :
    (∑ᶠ z ∈ SetOfZeros r f, (analyticOrderNatAt f z : ℝ)) ≤
      Real.log B / Real.log (R / r) := by
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  have hfin : (SetOfZeros r f).Finite := by
    apply finite_SetOfZeros_of_analytic (R := R) (r := r) r_lt_R
    · intro z hz
      exact hfAnalytic z (Metric.ball_subset_closedBall hz)
    · simp [R_pos]
    · rw [hf0_eq_one]
      exact one_ne_zero
  have hAnalytic_r : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) |r|) := by
    intro z hz
    apply hfAnalytic z
    have hz' : ‖z‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right, abs_of_pos r_pos] using hz
    have hzR : ‖z‖ ≤ R := hz'.trans r_lt_R.le
    simpa [Metric.mem_closedBall, dist_zero_right] using hzR
  have h0mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    simp [R_pos.le]
  have h0top : analyticOrderAt f (0 : ℂ) ≠ ⊤ := by
    have h0zero : analyticOrderAt f (0 : ℂ) = 0 :=
      (hfAnalytic 0 h0mem).analyticOrderAt_eq_zero.mpr (by
        rw [hf0_eq_one]
        exact one_ne_zero)
    rw [h0zero]
    simp
  have hsupport :
      Function.support
          (fun z => (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) |r|) z : ℝ)) ⊆
        SetOfZeros r f := by
    intro z hz
    have hzDreal :
        (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) |r|) z : ℝ) ≠ 0 := by
      simpa [Function.mem_support] using hz
    have hzD : MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) |r|) z ≠ 0 := by
      exact_mod_cast hzDreal
    have hzSupport :
        z ∈ (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) |r|)).support := by
      simpa [Function.mem_support] using hzD
    have hzr : z ∈ Metric.closedBall (0 : ℂ) |r| :=
      (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) |r|)).supportWithinDomain hzSupport
    have hzero : f z = 0 := by
      by_contra hfz
      have horder0 : analyticOrderAt f z = 0 :=
        (hAnalytic_r z hzr).analyticOrderAt_eq_zero.mpr hfz
      apply hzD
      rw [hAnalytic_r.divisor_apply hzr, horder0]
      simp
    have hnorm : ‖z‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right, abs_of_pos r_pos] using hzr
    exact ⟨hnorm, hzero⟩
  have hsum_eq :
      (∑ᶠ z ∈ SetOfZeros r f, (analyticOrderNatAt f z : ℝ)) =
        ∑ᶠ z, (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) |r|) z : ℝ) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
      finsum_eq_sum_of_support_subset_of_finite
        (fun z => (MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) |r|) z : ℝ))
        hsupport hfin]
    apply Finset.sum_congr rfl
    intro z hz
    have hzset : z ∈ SetOfZeros r f := hfin.mem_toFinset.mp hz
    have hzr : z ∈ Metric.closedBall (0 : ℂ) |r| := by
      simpa [Metric.mem_closedBall, dist_zero_right, abs_of_pos r_pos] using hzset.1
    have hzR : z ∈ Metric.closedBall (0 : ℂ) R := by
      have : ‖z‖ ≤ R := hzset.1.trans r_lt_R.le
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    have htop : analyticOrderAt f z ≠ ⊤ :=
      analyticOrderAt_ne_top_of_isPreconnected hfAnalytic Metric.isPreconnected_closedBall
        h0mem hzR h0top
    have hd :
        MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) |r|) z =
          (analyticOrderNatAt f z : ℤ) := by
      rw [hAnalytic_r.divisor_apply hzr]
      rw [← Nat.cast_analyticOrderNatAt htop]
      simp
    rw [hd]
    norm_cast
  rw [hsum_eq]
  exact jensenDivisorBound_normalized r_pos r_lt_R one_le_B hfAnalytic hf0_eq_one fz_bound

end AnalyticNumberTheory.ComplexAnalysis
