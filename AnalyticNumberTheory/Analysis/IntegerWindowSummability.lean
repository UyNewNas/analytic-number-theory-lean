/-
Copyright (c) 2026 UyNewNas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Source/API audit:
* pinned mathlib
  @ e4c91783ca8e6a7c693ae624ade32fd22d4e43c1,
  especially `summable_of_sum_le`, `Summable.sum_le_tsum`, integer ceiling
  lemmas, and `Finset.sum_fiberwise_of_maps_to`;
* anthropics/formal-math
  @ fbdc36bbf17d20af3fd0447c6d1a8a02773c9844,
  `zeta23/Zeta23/Tail/Basic.lean::LocalCount` and
  `zeta23/Zeta23/WeilEF/ZeroSummability.lean`, especially the integer-window
  key bookkeeping used by `zero_sum_inv_sq_gen`;
* canonical same-revision Goldbach
  @ 09b97db5764ade1246bfb77206baa1b124760958, where no competing packaged
  generic integer-window summability adapter was found;
* futuretechlab/rh-garden
  @ c95f07025015b334948b52eadb31be2f07786de8,
  `ZETA23_COMPATIBILITY.md`, which independently records that the reusable
  core of `zero_sum_inv_sq_gen` is much smaller than the full zeta23
  zero/explicit-formula hierarchy.

This file deliberately extracts only that neutral bookkeeping seam.  It has no
zero configuration, Dirichlet character, GRH premise, explicit-formula object,
or number-theoretic local-count theorem.  Concrete consumers supply their own
nonnegative summable window majorant.
-/

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

open scoped BigOperators

namespace AnalyticNumberTheory.Analysis

noncomputable section

/-- Integer key for the half-open unit window containing `y`: if
`n = integerWindowKey y`, then `n < y ≤ n + 1`. -/
def integerWindowKey (y : ℝ) : ℤ := ⌈y⌉ - 1

/-- The integer-window key lies strictly below the represented real point. -/
lemma integerWindowKey_lt (y : ℝ) : (integerWindowKey y : ℝ) < y := by
  have h := Int.ceil_lt_add_one y
  unfold integerWindowKey
  push_cast
  linarith

/-- The represented real point lies at or below the upper endpoint of its
integer unit window. -/
lemma le_integerWindowKey_add_one (y : ℝ) :
    y ≤ (integerWindowKey y : ℝ) + 1 := by
  have h := Int.le_ceil y
  unfold integerWindowKey
  push_cast
  linarith

/-- A nonnegative family is summable if every finite subfamily inside each
integer unit window is bounded by a summable window majorant.

This is the project-neutral finite-fiber core behind the standard passage from
unit-window zero counts to globally summable decaying zero weights. -/
theorem summable_of_integerWindow_sum_le
    {ι : Type*} (γ : ι → ℝ) (f : ι → ℝ) (bound : ℤ → ℝ)
    (hf : ∀ x, 0 ≤ f x)
    (hbound : Summable bound)
    (hwindow : ∀ n : ℤ, ∀ s : Finset ι,
      (∀ x ∈ s, (n : ℝ) < γ x ∧ γ x ≤ (n : ℝ) + 1) →
      ∑ x ∈ s, f x ≤ bound n) :
    Summable f := by
  classical
  have hbound_nonneg : ∀ n : ℤ, 0 ≤ bound n := by
    intro n
    have h := hwindow n ∅ (by simp)
    simpa using h
  refine summable_of_sum_le (c := ∑' n : ℤ, bound n) hf ?_
  intro s
  set κ : ι → ℤ := fun x => integerWindowKey (γ x)
  calc
    ∑ x ∈ s, f x =
        ∑ n ∈ s.image κ, ∑ x ∈ s with κ x = n, f x := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (g := κ) (t := s.image κ)
        (fun x hx => Finset.mem_image_of_mem κ hx)
    _ ≤ ∑ n ∈ s.image κ, bound n := by
      apply Finset.sum_le_sum
      intro n hn
      apply hwindow n (s.filter fun x => κ x = n)
      intro x hx
      simp only [Finset.mem_filter] at hx
      constructor
      · rw [← hx.2]
        simpa [κ] using integerWindowKey_lt (γ x)
      · rw [← hx.2]
        simpa [κ] using le_integerWindowKey_add_one (γ x)
    _ ≤ ∑' n : ℤ, bound n :=
      hbound.sum_le_tsum _ (fun n _ => hbound_nonneg n)

end

end AnalyticNumberTheory.Analysis
