/-
Copyright (c) 2026 UyNewNas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Source/API audit:
* `anthropics/formal-math@fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`,
  `zeta23/Zeta23/WeilEF/Landau.lean`, declarations
  `analyticAt_finset_prod_sub_pow` and `logDeriv_zero_prod`, and
  `zeta23/Zeta23/FromPNTPlus/StrongPNTPrefix.lean`, declaration
  `ZeroFactorization`.
* Pinned Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`,
  `Mathlib/Analysis/Calculus/LogDeriv.lean` and
  `Mathlib/Analysis/Analytic/Order.lean`, already provides
  `logDeriv_prod`, `logDeriv_fun_pow`, `logDeriv_apply`, and the
  local analytic-order factorization theorem.
* Canonical same-revision `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`
  has no packaged finite-zero-product logarithmic-derivative helper under this interface.

Only the local finite-zero algebra is extracted here.  No Jensen bound, zero-count theorem,
Dirichlet object, GRH premise, or application-specific parameter enters this module.
-/

import AnalyticNumberTheory.ComplexAnalysis.JensenZeros
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic

open Complex Set Filter

namespace AnalyticNumberTheory.ComplexAnalysis

noncomputable section

/-- A zero of an analytic function on a connected closed unit disc has a finite local order and
therefore admits the canonical local factorization by that order.

This is the assumption-explicit, choice-free public form of the source's `ZeroFactorization`:
the downstream regularized quotient can choose a value later, while this theorem keeps the
actual analytic factor and its nonvanishing witness visible. -/
theorem exists_analyticFactor_at_zero
    {R : ℝ} {f : ℂ → ℂ} {ρ : ℂ}
    (hR : R < 1)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf0 : f 0 ≠ 0)
    (hρ : ρ ∈ SetOfZeros R f) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      f =ᶠ[𝓝 ρ] fun z => (z - ρ) ^ analyticOrderNatAt f ρ • g z := by
  have hzero : 0 ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp
  have hρball : ρ ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
    exact hρ.1.trans hR.le
  have horder0 : analyticOrderAt f 0 = 0 := by
    rw [analyticOrderAt_eq_zero]
    exact Or.inr hf0
  have hfinite : analyticOrderAt f ρ ≠ ⊤ := by
    apply hf.analyticOrderAt_ne_top_of_isPreconnected Metric.isPreconnected_closedBall
      hzero hρball
    rw [horder0]
    exact ENat.zero_ne_top
  have hanalytic : AnalyticAt ℂ f ρ := hf ρ hρball
  exact hanalytic.analyticOrderAt_ne_top.mp hfinite

/-- A finite product of shifted polynomial powers is analytic everywhere. -/
theorem analyticAt_finsetProd_sub_pow (s : Finset ℂ) (m : ℂ → ℕ) (w : ℂ) :
    AnalyticAt ℂ (fun z => ∏ ρ ∈ s, (z - ρ) ^ m ρ) w := by
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.prod_empty]
      exact analyticAt_const
  | @insert a s hs ih =>
      have hfun :
          (fun z => ∏ ρ ∈ insert a s, (z - ρ) ^ m ρ) =
            fun z => (z - a) ^ m a * ∏ ρ ∈ s, (z - ρ) ^ m ρ := by
        funext z
        rw [Finset.prod_insert hs]
      rw [hfun]
      exact ((analyticAt_id.sub analyticAt_const).pow _).mul ih

/-- Logarithmic derivative of a finite zero polynomial.

At a point avoiding every listed zero, the logarithmic derivative of
`∏ρ (z - ρ)^(m ρ)` is exactly `∑ρ m ρ / (z - ρ)`.
-/
theorem logDeriv_finsetProd_sub_pow
    {s : Finset ℂ} {m : ℂ → ℕ} {z : ℂ}
    (hz : ∀ ρ ∈ s, z ≠ ρ) :
    logDeriv (fun w => ∏ ρ ∈ s, (w - ρ) ^ m ρ) z =
      ∑ ρ ∈ s, (m ρ : ℂ) / (z - ρ) := by
  rw [logDeriv_prod (f := fun ρ w => (w - ρ) ^ m ρ)
    (fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hz ρ hρ)))
    (fun ρ _ => by fun_prop)]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hd : HasDerivAt (fun w : ℂ => w - ρ) 1 z :=
    (hasDerivAt_id z).sub_const ρ
  rw [logDeriv_fun_pow hd.differentiableAt, logDeriv_apply, hd.deriv]
  ring

end

end AnalyticNumberTheory.ComplexAnalysis
