/-
Copyright (c) 2026 UyNewNas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Source/API audit:
* PalomarArchive/anthropics--zeta-23-lean--94784dd69547
  @ cec57f919ccf34e5fa5372b4ba332f7c848bbb6e,
  `Zeta23/RvM/ReZeroCount.lean`, theorem `finite_zeros_closedBall`.
* The source pins a different mathlib revision.  This file re-proves only the
  project-neutral isolated-zero/compactness lemma against ANT's pinned mathlib.
* Pinned mathlib already provides the isolated-zero principle
  `AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected`; it does not
  package this closed-ball finiteness consequence under the audited interface.
-/

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

open Filter Set

namespace AnalyticNumberTheory.ComplexAnalysis

/-- Zeros of a complex analytic function on a closed sub-ball are finite if the
function is analytic on a larger open ball and is nonzero at one point there.

This is the neutral compactness corollary of the isolated-zero principle used
by Jensen/zero-count arguments. -/
theorem finite_zeros_closedBall {f : ℂ → ℂ} {R r : ℝ} (hrR : r < R)
    (hA : AnalyticOnNhd ℂ f (Metric.ball 0 R)) {z₀ : ℂ} (hz₀ : z₀ ∈ Metric.ball 0 R)
    (hfz₀ : f z₀ ≠ 0) : {z : ℂ | ‖z‖ ≤ r ∧ f z = 0}.Finite := by
  have hU : IsPreconnected (Metric.ball (0 : ℂ) R) := (convex_ball 0 R).isPreconnected
  rcases hA.eqOn_zero_or_eventually_ne_zero_of_preconnected hU with h0 | hcod
  · exact absurd (h0 hz₀) hfz₀
  rw [Filter.Eventually, codiscreteWithin_iff_locallyFiniteComplementWithin] at hcod
  have hsub : Metric.closedBall (0 : ℂ) r ⊆ Metric.ball 0 R :=
    Metric.closedBall_subset_ball hrR
  have hloc : ∀ z ∈ Metric.closedBall (0 : ℂ) r, ∃ t ∈ nhds z,
      (t ∩ {x : ℂ | x ∈ Metric.ball (0 : ℂ) R ∧ f x = 0}).Finite := by
    intro z hz
    obtain ⟨t, ht, hfin⟩ := hcod z (hsub hz)
    refine ⟨t, ht, hfin.subset ?_⟩
    rintro x ⟨hxt, hxU, hx0⟩
    exact ⟨hxt, hxU, by simpa using hx0⟩
  choose t ht hfin using hloc
  obtain ⟨I, hcover⟩ := (isCompact_closedBall (0 : ℂ) r).elim_nhds_subcover' t ht
  refine ((I.finite_toSet.biUnion fun z _ => hfin z z.2).subset ?_)
  rintro x ⟨hxr, hx0⟩
  have hxball : x ∈ Metric.closedBall (0 : ℂ) r := by
    rwa [Metric.mem_closedBall, dist_zero_right]
  obtain ⟨z, hzI, hxz⟩ := Set.mem_iUnion₂.mp (hcover hxball)
  exact Set.mem_iUnion₂.mpr ⟨z, hzI, hxz, hsub hxball, hx0⟩

end AnalyticNumberTheory.ComplexAnalysis
