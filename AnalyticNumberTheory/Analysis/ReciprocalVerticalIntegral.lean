/-
Copyright (c) 2026 UyNewNas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Source/API audit:
* provenance-preserving adaptation from
  `subfish-zhou/liu-wang-ternary-goldbach-lean`
  @ `b57b7307810c37267e47110d8b5f920e3e681c81`;
* source modules:
  `BombieriVinogradov/Helpers/RealAnalysis/OneDivAbsIntegral.lean`,
  `.../LogOverOnePlusAbsContinuity.lean`, and
  `.../LogOverOnePlusAbsIntegral.lean`;
* the source is on the exact same pinned Mathlib revision
  `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`;
* only project-neutral real-analysis lemmas are adapted here.  No contour,
  Dirichlet-character, zero-count, or application-specific API is imported.
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace AnalyticNumberTheory.Analysis

/-- Exact symmetric reciprocal-weight integral used by vertical-contour bounds. -/
theorem intervalIntegralOneDivAbsAddOne
    (T : ℝ) (hT : 0 ≤ T) :
    intervalIntegral (fun t : ℝ => 1 / (|t| + 1))
        (-T) T MeasureTheory.volume =
      2 * Real.log (T + 1) := by
  let f : ℝ → ℝ := fun t => 1 / (|t| + 1)
  have hfContinuous : Continuous f := by
    dsimp [f]
    exact continuous_const.div (continuous_abs.add continuous_const)
      (fun t => by positivity)
  have hfNeg : IntervalIntegrable f MeasureTheory.volume (-T) 0 :=
    hfContinuous.intervalIntegrable _ _
  have hfPos : IntervalIntegrable f MeasureTheory.volume 0 T :=
    hfContinuous.intervalIntegrable _ _
  have hSplit :
      intervalIntegral f (-T) T MeasureTheory.volume =
        intervalIntegral f (-T) 0 MeasureTheory.volume +
          intervalIntegral f 0 T MeasureTheory.volume :=
    (intervalIntegral.integral_add_adjacent_intervals hfNeg hfPos).symm
  have hNegEq :
      intervalIntegral f (-T) 0 MeasureTheory.volume =
        intervalIntegral f 0 T MeasureTheory.volume := by
    have hComp :=
      intervalIntegral.integral_comp_neg
        (f := f) (a := 0) (b := T)
    simpa [f] using hComp.symm
  have hPos :
      intervalIntegral f 0 T MeasureTheory.volume =
        Real.log (T + 1) := by
    have hShift :=
      intervalIntegral.integral_comp_add_right
        (f := fun u : ℝ => u ^ (-1 : Int))
        (a := 0) (b := T) 1
    have hInv :=
      integral_inv_of_pos
        (a := (1 : ℝ)) (b := T + 1)
        (by norm_num) (by linarith)
    calc
      intervalIntegral f 0 T MeasureTheory.volume =
          intervalIntegral (fun t : ℝ => (t + 1) ^ (-1 : Int))
            0 T MeasureTheory.volume := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht0 : 0 ≤ t := by
          rw [Set.uIcc_of_le hT] at ht
          exact ht.1
        simp [abs_of_nonneg ht0]
      _ = intervalIntegral (fun u : ℝ => u ^ (-1 : Int))
            1 (T + 1) MeasureTheory.volume := by
        simpa only [zero_add] using hShift
      _ = Real.log ((T + 1) / 1) := by
        simpa only [zpow_neg_one] using hInv
      _ = Real.log (T + 1) := by simp
  rw [hSplit, hNegEq, hPos]
  ring

/-- Continuity of the logarithmically weighted reciprocal majorant. -/
theorem continuousLogWeightDivAbsAddOne
    (A C : ℝ) :
    Continuous (fun t : ℝ =>
      (A + C * Real.log (|t| + 2)) *
        (6 / (|t| + 1))) := by
  have hAbsOne : Continuous (fun t : ℝ => |t| + 1) :=
    continuous_abs.add continuous_const
  have hAbsTwo : Continuous (fun t : ℝ => |t| + 2) :=
    continuous_abs.add continuous_const
  have hSixReciprocal :
      Continuous (fun t : ℝ => 6 / (|t| + 1)) :=
    continuous_const.div hAbsOne (fun t => by positivity)
  have hLog : Continuous (fun t : ℝ => Real.log (|t| + 2)) :=
    hAbsTwo.log (fun t => by positivity)
  exact (continuous_const.add (continuous_const.mul hLog)).mul hSixReciprocal

/-- Finite-interval integrability of the logarithmically weighted reciprocal majorant. -/
theorem intervalIntegrableLogWeightDivAbsAddOne
    (A C T : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        (A + C * Real.log (|t| + 2)) *
          (6 / (|t| + 1)))
      MeasureTheory.volume (-T) T :=
  (continuousLogWeightDivAbsAddOne A C).intervalIntegrable _ _

/-- Freeze the monotone logarithmic numerator at the symmetric interval endpoint.
The result is the neutral vertical-edge estimate needed by downstream Perron contours. -/
theorem intervalIntegralLogWeightDivAbsAddOneLe
    (A C T : ℝ) (hC : 0 ≤ C) (hT : 0 ≤ T) :
    intervalIntegral
        (fun t : ℝ =>
          (A + C * Real.log (|t| + 2)) *
            (6 / (|t| + 1)))
        (-T) T MeasureTheory.volume ≤
      12 * (A + C * Real.log (T + 2)) *
        Real.log (T + 1) := by
  let f : ℝ → ℝ := fun t =>
    (A + C * Real.log (|t| + 2)) *
      (6 / (|t| + 1))
  let K : ℝ := A + C * Real.log (T + 2)
  let g : ℝ → ℝ := fun t => K * (6 / (|t| + 1))
  have hfIntegrable :
      IntervalIntegrable f MeasureTheory.volume (-T) T := by
    exact intervalIntegrableLogWeightDivAbsAddOne A C T
  have hgIntegrable :
      IntervalIntegrable g MeasureTheory.volume (-T) T := by
    simpa [g, K] using
      intervalIntegrableLogWeightDivAbsAddOne K 0 T
  have hPointwise :
      ∀ t : ℝ, (Set.Icc (-T) T) t → f t ≤ g t := by
    intro t ht
    have htAbs : |t| ≤ T := abs_le.mpr ⟨ht.1, ht.2⟩
    have hLogBound :
        Real.log (|t| + 2) ≤ Real.log (T + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hWeight :
        A + C * Real.log (|t| + 2) ≤ K := by
      dsimp [K]
      exact add_le_add_right (mul_le_mul_of_nonneg_left hLogBound hC) A
    have hKernelNonneg : 0 ≤ 6 / (|t| + 1) := by positivity
    dsimp [f, g]
    exact mul_le_mul_of_nonneg_right hWeight hKernelNonneg
  have hMono :
      intervalIntegral f (-T) T MeasureTheory.volume ≤
        intervalIntegral g (-T) T MeasureTheory.volume :=
    intervalIntegral.integral_mono_on (by linarith)
      hfIntegrable hgIntegrable hPointwise
  calc
    intervalIntegral
        (fun t : ℝ =>
          (A + C * Real.log (|t| + 2)) *
            (6 / (|t| + 1)))
        (-T) T MeasureTheory.volume =
      intervalIntegral f (-T) T MeasureTheory.volume := by rfl
    _ ≤ intervalIntegral g (-T) T MeasureTheory.volume := hMono
    _ = K * intervalIntegral
          (fun t : ℝ => 6 / (|t| + 1))
          (-T) T MeasureTheory.volume := by
      dsimp [g]
      rw [intervalIntegral.integral_const_mul]
    _ = K * (6 * intervalIntegral
          (fun t : ℝ => 1 / (|t| + 1))
          (-T) T MeasureTheory.volume) := by
      congr 1
      rw [show (fun t : ℝ => 6 / (|t| + 1)) =
          fun t : ℝ => 6 * (1 / (|t| + 1)) by
        funext t
        ring]
      rw [intervalIntegral.integral_const_mul]
    _ = 12 * (A + C * Real.log (T + 2)) *
        Real.log (T + 1) := by
      rw [intervalIntegralOneDivAbsAddOne T hT]
      dsimp [K]
      ring

end AnalyticNumberTheory.Analysis
