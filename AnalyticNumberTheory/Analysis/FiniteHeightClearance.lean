/-
Copyright (c) 2026 UyNewNas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Source/API audit:
* `subfish-zhou/liu-wang-ternary-goldbach-lean`
  @ `b57b7307810c37267e47110d8b5f920e3e681c81`,
  `LiuWang/Proof/DirichletZeroCount/Applications/ClosedHeight.lean`,
  theorem `finite_height_clearance` (source blob
  `c327d3d5be1e9ac47aa7626fe4ae4765468a0d32`).
* The source theorem sits below a larger Dirichlet zero-count hierarchy.  This
  file source-adapts only the project-neutral finite-set clearance argument and
  a thin finite-height corollary; no zero-count, character, GRH, or contour API
  is migrated.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Classical

namespace AnalyticNumberTheory.Analysis

/-- A finite set of complex points has a positive one-sided gap above any
reference height, measured using absolute imaginary parts.

This is the finite combinatorial core of regular-height selection: no analytic
or number-theoretic hypothesis is used. -/
theorem finiteHeightClearance (F : Finset ℂ) (y : ℝ) :
    ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧
      ∀ z ∈ F, y < |z.im| → y + e < |z.im| := by
  induction F using Finset.induction_on with
  | empty =>
      exact ⟨1, by norm_num, le_rfl, by simp⟩
  | @insert z F hnot ih =>
      obtain ⟨e, he, he1, hgap⟩ := ih
      by_cases hz : y < |z.im|
      · refine ⟨min e ((|z.im| - y) / 2), lt_min he (by linarith),
          (min_le_left _ _).trans he1, ?_⟩
        intro w hw hwy
        rcases Finset.mem_insert.mp hw with rfl | hw
        · have h := min_le_right e ((|w.im| - y) / 2)
          linarith
        · have hg := hgap w hw hwy
          have hm := min_le_left e ((|z.im| - y) / 2)
          linarith
      · refine ⟨e, he, he1, ?_⟩
        intro w hw hwy
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact (hz hwy).elim
        · exact hgap w hw hwy

/-- Given finitely many complex points and any positive interval length, choose
an interior height that is different from every absolute imaginary part in the
finite set.

This packages the immediately reusable consequence of `finiteHeightClearance`
without importing any Dirichlet-zero infrastructure. -/
theorem existsHeightAvoidingFiniteImaginaryParts (F : Finset ℂ)
    {y r : ℝ} (hr : 0 < r) :
    ∃ H : ℝ, y < H ∧ H < y + r ∧ ∀ z ∈ F, |z.im| ≠ H := by
  obtain ⟨e, he, _he1, hgap⟩ := finiteHeightClearance F y
  let d := min e (r / 2)
  have hd : 0 < d := lt_min he (by linarith)
  have hde : d ≤ e := min_le_left _ _
  have hdr : d ≤ r / 2 := min_le_right _ _
  refine ⟨y + d, by linarith, by linarith, ?_⟩
  intro z hz hEq
  have hyH : y < y + d := by linarith
  have hyabs : y < |z.im| := by
    rw [hEq]
    exact hyH
  have hstrict := hgap z hz hyabs
  rw [hEq] at hstrict
  linarith

end AnalyticNumberTheory.Analysis
