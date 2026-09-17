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

The pinned mathlib theorem is stronger and more canonical than copying the
upstream Blaschke/Borel--Caratheodory implementation.  This module therefore
adds only a normalized-origin thin adapter; it does not duplicate Jensen's
formula or the upstream `ZerosBound` proof.
-/

import AnalyticNumberTheory.ComplexAnalysis.JensenZeros
import Mathlib.Analysis.Complex.JensenFormula

namespace AnalyticNumberTheory.ComplexAnalysis

/-- Quantitative Jensen zero-multiplicity bound at the origin, specialized to
`f 0 = 1`.

This is a thin adapter around pinned mathlib's
`AnalyticOnNhd.sum_divisor_le`.  In particular, multiplicities are carried by
mathlib's analytic divisor rather than by a project-specific zero-count
axiom. -/
theorem jensenDivisorBound_normalized {B r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (one_le_B : 1 ≤ B)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    (hf0_eq_one : f 0 = 1)
    (fz_bound : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∑ᶠ u, MeromorphicOn.divisor f (Metric.closedBall (0 : ℂ) r) u ≤
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
  simpa [abs_of_pos r_pos, abs_of_pos R_pos, hf0_eq_one] using h

end AnalyticNumberTheory.ComplexAnalysis
