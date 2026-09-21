/-
Copyright (c) 2026 UyNewNas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Source/API audit:
* Pinned Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` defines
  `Complex.digamma = logDeriv Complex.Gamma`, proves meromorphicity, and supplies
  `Complex.differentiableAt_Gamma` / `Complex.Gamma_ne_zero`, but does not package
  right-half-plane analyticity of `digamma`.
* `anthropics/formal-math@fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`,
  `zeta23/Zeta23/ThmE/GammaFactsChiProof.lean::analyticAt_digamma'`, gives the
  same neutral regularity seam on a different Mathlib revision.
* Exact-same-pin `subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`
  uses stronger quantitative digamma/gamma-factor bounds downstream but does not expose
  this small theorem as an independent reusable API.

This module source-adapts only the positive-half-plane analyticity fact.  It introduces no
Dirichlet character, zero-free/GRH hypothesis, Stirling estimate, digamma series, or application
parameter.
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Tactic

namespace AnalyticNumberTheory.ComplexAnalysis

private lemma gamma_ne_neg_nat_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ∀ m : ℕ, z ≠ -m := by
  intro m h
  rw [h] at hz
  simp only [Complex.neg_re, Complex.natCast_re] at hz
  exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg m))) hz

/-- The complex digamma function is analytic at every point in the open right half-plane. -/
theorem analyticAt_digamma_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.digamma z := by
  have hU : IsOpen {w : ℂ | 0 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hGammaDiff : DifferentiableOn ℂ Complex.Gamma {w : ℂ | 0 < w.re} := fun w hw =>
    (Complex.differentiableAt_Gamma w (gamma_ne_neg_nat_of_re_pos hw)).differentiableWithinAt
  have hGammaAnalytic := hGammaDiff.analyticOnNhd hU
  have hDeriv : AnalyticAt ℂ (deriv Complex.Gamma) z := (hGammaAnalytic z hz).deriv
  have hGamma : AnalyticAt ℂ Complex.Gamma z := hGammaAnalytic z hz
  have hGammaNe : Complex.Gamma z ≠ 0 :=
    Complex.Gamma_ne_zero (gamma_ne_neg_nat_of_re_pos hz)
  have hQuot := hDeriv.div hGamma hGammaNe
  exact hQuot.congr (by
    filter_upwards with w
    rw [Complex.digamma_def, logDeriv_apply]
    rfl)

end AnalyticNumberTheory.ComplexAnalysis
