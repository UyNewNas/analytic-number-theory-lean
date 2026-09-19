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
* The same source commit also contains the project-neutral quantitative grid
  lemma `BombieriVinogradov.RealAnalysis.exists_unitInterval_away_from_finset`
  in `BombieriVinogradov/Helpers/RealAnalysis/FiniteSetIntervalAvoidance.lean`
  (source blob `2df92dcf0cd3d9eba6f9e54cfdf60a2ca22f0ed8`).  ANT adapts only that finite
  real-set pigeonhole statement below; the source's Dirichlet zero selector,
  local zero count, and logarithmic-derivative hierarchy are not migrated.
* The source theorem sits below a larger Dirichlet zero-count hierarchy.  This
  file source-adapts only project-neutral finite-set clearance arguments; no
  zero-count, character, GRH, or contour API is migrated.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Classical

namespace AnalyticNumberTheory.Analysis

/-- A finite set of real numbers can be avoided inside every unit interval with
explicit separation at least `1 / (2 * (card + 2))`.

This is a provenance-preserving adaptation of Liu--Wang's neutral
`exists_unitInterval_away_from_finset`.  It is the quantitative combinatorial
seam needed by downstream selected-height arguments; no analytic or
number-theoretic hypothesis is used. -/
theorem existsUnitIntervalAwayFromFinset
    (s : Finset ℝ) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧ t ≤ T + 1 ∧
      ∀ x : s,
        1 / (2 * ((s.card : ℝ) + 2)) ≤ |t - (x : ℝ)| := by
  classical
  let denominator : ℝ := (s.card : ℝ) + 2
  let radius : ℝ := 1 / (2 * denominator)
  let grid : Fin (s.card + 1) → ℝ := fun k =>
    T + ((k.val + 1 : ℕ) : ℝ) / denominator
  have hDenPos : 0 < denominator := by
    dsimp [denominator]
    positivity
  have hGridLower : ∀ k : Fin (s.card + 1), T ≤ grid k := by
    intro k
    have hNumNonneg : 0 ≤ ((k.val + 1 : ℕ) : ℝ) := by
      positivity
    have hFracNonneg :
        0 ≤ ((k.val + 1 : ℕ) : ℝ) / denominator :=
      div_nonneg hNumNonneg (le_of_lt hDenPos)
    dsimp [grid]
    linarith
  have hGridUpper : ∀ k : Fin (s.card + 1), grid k ≤ T + 1 := by
    intro k
    have hkNat : k.val + 1 ≤ s.card + 2 :=
      Nat.le_trans (Nat.succ_le_iff.mpr k.isLt)
        (Nat.le_succ (s.card + 1))
    have hkCast : ((k.val + 1 : ℕ) : ℝ) ≤ denominator := by
      have hkCastRaw :
          ((k.val + 1 : ℕ) : ℝ) ≤ ((s.card + 2 : ℕ) : ℝ) :=
        (Nat.cast_le).2 hkNat
      simpa [denominator] using hkCastRaw
    have hFracLe :
        ((k.val + 1 : ℕ) : ℝ) / denominator ≤ 1 :=
      (div_le_one hDenPos).2 hkCast
    dsimp [grid]
    linarith
  by_cases hGood : ∃ k : Fin (s.card + 1),
      ∀ x : s, radius ≤ |grid k - (x : ℝ)|
  · obtain ⟨k, hk⟩ := hGood
    exact ⟨grid k, hGridLower k, hGridUpper k, by
      intro x
      simpa [radius, denominator] using hk x⟩
  · have hBad : ∀ k : Fin (s.card + 1),
        ∃ x : s, |grid k - (x : ℝ)| < radius := by
      intro k
      by_contra hNone
      apply hGood
      exact ⟨k, fun x => le_of_not_gt (fun hx => hNone ⟨x, hx⟩)⟩
    let chosen : Fin (s.card + 1) → s := fun k =>
      Classical.choose (hBad k)
    have hChosen : ∀ k : Fin (s.card + 1),
        |grid k - (chosen k : ℝ)| < radius := by
      intro k
      exact Classical.choose_spec (hBad k)
    have hCard :
        Fintype.card s < Fintype.card (Fin (s.card + 1)) := by
      simp
    obtain ⟨k, l, hkl, hEq⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt chosen hCard
    have hCloseRight :
        |(chosen k : ℝ) - grid l| < radius := by
      have hl := hChosen l
      rw [abs_sub_comm] at hl
      simpa [hEq] using hl
    have hClose : |grid k - grid l| < 2 * radius := by
      calc
        |grid k - grid l| ≤
            |grid k - (chosen k : ℝ)| +
              |(chosen k : ℝ) - grid l| :=
          abs_sub_le _ _ _
        _ < radius + radius :=
          add_lt_add (hChosen k) hCloseRight
        _ = 2 * radius := by ring
    have hValNe : k.val ≠ l.val := by
      intro hVal
      exact hkl (Fin.ext hVal)
    have hIndexGap :
        (1 : ℝ) ≤ |(k.val : ℝ) - (l.val : ℝ)| :=
      Or.elim (lt_or_gt_of_ne hValNe)
        (fun hlt => by
          have hNat : k.val + 1 ≤ l.val :=
            Nat.succ_le_iff.mpr hlt
          have hCast : (k.val : ℝ) + 1 ≤ (l.val : ℝ) := by
            have hCastRaw :
                ((k.val + 1 : ℕ) : ℝ) ≤ (l.val : ℝ) :=
              (Nat.cast_le).2 hNat
            simpa using hCastRaw
          rw [abs_of_nonpos (by linarith)]
          linarith)
        (fun hgt => by
          have hNat : l.val + 1 ≤ k.val :=
            Nat.succ_le_iff.mpr hgt
          have hCast : (l.val : ℝ) + 1 ≤ (k.val : ℝ) := by
            have hCastRaw :
                ((l.val + 1 : ℕ) : ℝ) ≤ (k.val : ℝ) :=
              (Nat.cast_le).2 hNat
            simpa using hCastRaw
          rw [abs_of_nonneg (by linarith)]
          linarith)
    have hGridDifference :
        grid k - grid l =
          ((k.val : ℝ) - (l.val : ℝ)) * (1 / denominator) := by
      dsimp [grid]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    have hGridGap : 1 / denominator ≤ |grid k - grid l| := by
      rw [hGridDifference, abs_mul, abs_of_pos (by positivity :
        0 < (1 / denominator))]
      simpa using
        mul_le_mul_of_nonneg_right hIndexGap
          (le_of_lt (show 0 < 1 / denominator by positivity))
    have hTwiceRadius : 2 * radius = 1 / denominator := by
      dsimp [radius]
      field_simp
    linarith

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
