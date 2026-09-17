/-
Copyright (c) 2026 UyNewNas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Source/API audit:
* AlexKontorovich/PrimeNumberTheoremAnd
  @ a5154676af9aa3095150ee410cdda80555aa0642,
  `PrimeNumberTheoremAnd/StrongPNT.lean`, declarations `SetOfZeros` and
  `finiteSetOfZeros_mono`.
* AxiomMath/PrimeNumberTheoremAnd
  @ 75c7dffd3ddfe2bda7c33264c780a97486f8303d retains the same Jensen prefix.
* PalomarArchive/anthropics--zeta-23-lean--94784dd69547
  @ cec57f919ccf34e5fa5372b4ba332f7c848bbb6e consumes this prefix in the
  Dirichlet-character local-zero-count argument.
* Canonical same-revision `subfish-zhou/goldbach-lean`
  @ 09b97db5764ade1246bfb77206baa1b124760958 has no packaged `SetOfZeros`
  / Jensen-zero prefix under this interface.

This module extracts only the project-neutral zero-set bookkeeping needed before
Jensen's quantitative `ZerosBound`.  The compactness/isolated-zero theorem itself
is already proved in `FiniteZeros.lean` against ANT's pinned mathlib.
-/

import AnalyticNumberTheory.ComplexAnalysis.FiniteZeros

open Set

namespace AnalyticNumberTheory.ComplexAnalysis

/-- Zeros of `f` in the closed disc of radius `R`, counted only as a set.
Multiplicity is handled separately by `analyticOrderNatAt` in Jensen bounds. -/
def SetOfZeros (R : ℝ) (f : ℂ → ℂ) : Set ℂ :=
  {z : ℂ | ‖z‖ ≤ R ∧ f z = 0}

@[simp] theorem mem_SetOfZeros {R : ℝ} {f : ℂ → ℂ} {z : ℂ} :
    z ∈ SetOfZeros R f ↔ ‖z‖ ≤ R ∧ f z = 0 :=
  Iff.rfl

/-- Closed-disc zero sets are monotone in the radius. -/
theorem SetOfZeros_mono {r R : ℝ} {f : ℂ → ℂ} (hrR : r ≤ R) :
    SetOfZeros r f ⊆ SetOfZeros R f := by
  rw [SetOfZeros, SetOfZeros]
  rintro z ⟨hz, hzero⟩
  exact ⟨hz.trans hrR, hzero⟩

/-- Finiteness of the zero set descends to a smaller closed disc.

This is the radius-general form of the upstream `finiteSetOfZeros_mono` helper.
-/
theorem finiteSetOfZeros_mono {r R : ℝ} {f : ℂ → ℂ} (hrR : r ≤ R)
    (finiteZeros : (SetOfZeros R f).Finite) : (SetOfZeros r f).Finite :=
  finiteZeros.subset (SetOfZeros_mono hrR)

/-- Package `finite_zeros_closedBall` directly in the Jensen `SetOfZeros`
interface.  This is the exact bridge needed by downstream Jensen zero counts. -/
theorem finite_SetOfZeros_of_analytic {f : ℂ → ℂ} {R r : ℝ} (hrR : r < R)
    (hA : AnalyticOnNhd ℂ f (Metric.ball 0 R)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Metric.ball 0 R) (hfz₀ : f z₀ ≠ 0) :
    (SetOfZeros r f).Finite := by
  simpa [SetOfZeros] using
    (finite_zeros_closedBall (f := f) (R := R) (r := r) hrR hA hz₀ hfz₀)

end AnalyticNumberTheory.ComplexAnalysis
