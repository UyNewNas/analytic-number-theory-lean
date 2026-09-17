/-
Copyright (c) 2026 UyNewNas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Source/API audit:
* pinned mathlib @ e4c91783ca8e6a7c693ae624ade32fd22d4e43c1,
  especially `Mathlib/Analysis/PSeries.lean` (`Real.summable_abs_int_rpow`) and
  `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` (`Real.log_le_rpow_div`);
* anthropics/formal-math
  @ fbdc36bbf17d20af3fd0447c6d1a8a02773c9844,
  `zeta23/Zeta23/WeilEF/ZeroSummability.lean`, declarations `weight_le`,
  `summable_weight`, `key`, `key_lt`, `le_key_add_one`, and `one_add_sq_ge`;
* canonical same-revision subfish-zhou/goldbach-lean
  @ 09b97db5764ade1246bfb77206baa1b124760958: no competing packaged
  integer-window reciprocal-square/log-weight summability API was found.

Only the project-neutral integer-window geometry and summability seam is kept
here.  No `ZeroConfig`, zeta-zero, Dirichlet-L, GRH, or Liouville-specific
object is imported.
-/

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace AnalyticNumberTheory.ComplexAnalysis

/-- The logarithmic reciprocal-square weight on integer windows is controlled
by a summable `|n|^{-3/2}` majorant away from the origin. -/
theorem integerLogWeight_le (n : ℤ) (hn : n ≠ 0) :
    Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) ≤
      4 * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    exact_mod_cast Int.one_le_abs hn
  have hn0 : (0 : ℝ) < |(n : ℝ)| := by linarith
  have h1 := Real.log_le_rpow_div
    (show (0 : ℝ) ≤ |(n : ℝ)| + 3 by positivity)
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have h2 : (|(n : ℝ)| + 3) ^ (1 / 2 : ℝ) ≤
      (4 * |(n : ℝ)|) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have h3 : (4 * |(n : ℝ)|) ^ (1 / 2 : ℝ) =
      2 * |(n : ℝ)| ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hn0.le,
      show (4 : ℝ) ^ (1 / 2 : ℝ) = 2 by
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num,
          ← Real.rpow_mul (by norm_num)]
        norm_num]
  have hA : Real.log (|(n : ℝ)| + 3) ≤
      4 * |(n : ℝ)| ^ (1 / 2 : ℝ) := by
    have hdiv : (|(n : ℝ)| + 3) ^ (1 / 2 : ℝ) / (1 / 2) =
        2 * (|(n : ℝ)| + 3) ^ (1 / 2 : ℝ) := by ring
    rw [hdiv] at h1
    rw [h3] at h2
    linarith
  have hB : 1 / (1 + (n : ℝ) ^ 2) ≤ |(n : ℝ)| ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hn0.le,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, sq_abs, one_div]
    exact inv_anti₀ (by positivity) (by linarith)
  calc
    Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) =
        Real.log (|(n : ℝ)| + 3) * (1 / (1 + (n : ℝ) ^ 2)) := by ring
    _ ≤ (4 * |(n : ℝ)| ^ (1 / 2 : ℝ)) * |(n : ℝ)| ^ (-2 : ℝ) :=
      mul_le_mul hA hB (by positivity) (by positivity)
    _ = 4 * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
      rw [mul_assoc, ← Real.rpow_add hn0]
      norm_num

/-- `log(|n|+3)/(1+n^2)` is summable over `ℤ`.  This is the neutral summability
input used when unit-height local counts are converted into global zero sums. -/
theorem summable_integerLogWeight :
    Summable (fun n : ℤ =>
      Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by
  refine Summable.of_norm_bounded_eventually
    ((Real.summable_abs_int_rpow (show (1 : ℝ) < 3 / 2 by norm_num)).mul_left 4) ?_
  filter_upwards [eventually_cofinite_ne 0] with n hn
  have h0 : 0 ≤ Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) :=
    div_nonneg
      (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)]))
      (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact integerLogWeight_le n hn

/-- Integer window key `⌈y⌉ - 1`; it puts `y` in `(key y, key y + 1]`. -/
def integerWindowKey (y : ℝ) : ℤ := ⌈y⌉ - 1

/-- Lower endpoint inequality for `integerWindowKey`. -/
theorem integerWindowKey_lt (y : ℝ) : (integerWindowKey y : ℝ) < y := by
  have h := Int.ceil_lt_add_one y
  unfold integerWindowKey
  push_cast
  linarith

/-- Upper endpoint inequality for `integerWindowKey`. -/
theorem le_integerWindowKey_add_one (y : ℝ) :
    y ≤ (integerWindowKey y : ℝ) + 1 := by
  have h := Int.le_ceil y
  unfold integerWindowKey
  push_cast
  linarith

/-- If `n < y ≤ n+1`, then the reciprocal-square denominator at `y` controls
that of the integer window up to the absolute factor `4`. -/
theorem one_add_sq_ge_integerWindow {y : ℝ} {n : ℤ}
    (h1 : (n : ℝ) < y) (h2 : y ≤ (n : ℝ) + 1) :
    (1 + (n : ℝ) ^ 2) / 4 ≤ 1 + y ^ 2 := by
  rcases le_or_gt 0 (n : ℝ) with hn | hn
  · nlinarith
  · have hn' : n < 0 := by exact_mod_cast hn
    have hn1 : (n : ℝ) ≤ -1 := by
      exact_mod_cast (show n ≤ -1 by omega)
    have hy : ((n : ℝ) + 1) ^ 2 ≤ y ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h2)
        (by linarith : (0 : ℝ) ≤ -(y + ((n : ℝ) + 1)))]
    nlinarith [hy, sq_nonneg ((n : ℝ) + 4 / 3)]

end AnalyticNumberTheory.ComplexAnalysis
