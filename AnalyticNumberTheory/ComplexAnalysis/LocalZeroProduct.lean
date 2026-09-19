/-
Copyright (c) 2026 UyNewNas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Source/API audit:
* `anthropics/formal-math@fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`,
  `zeta23/Zeta23/WeilEF/Landau.lean`, declarations
  `analyticAt_finset_prod_sub_pow` and `logDeriv_zero_prod`.
* Pinned Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`,
  `Mathlib/Analysis/Calculus/LogDeriv.lean`, already provides
  `logDeriv_prod`, `logDeriv_fun_pow`, and `logDeriv_apply`.
* Canonical same-revision `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`
  has no packaged finite-zero-product logarithmic-derivative helper under this interface.

Only the finite-product algebra is extracted here.  No Jensen bound, zero-count theorem,
Dirichlet object, GRH premise, or application-specific parameter enters this module.
-/

import AnalyticNumberTheory.ComplexAnalysis.JensenZeros
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic

open Complex

namespace AnalyticNumberTheory.ComplexAnalysis

noncomputable section

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
