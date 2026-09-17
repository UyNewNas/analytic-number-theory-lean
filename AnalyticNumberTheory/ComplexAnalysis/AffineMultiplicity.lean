/-
Copyright (c) 2026 UyNewNas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Source/API audit:
* Pinned mathlib
  @ e4c91783ca8e6a7c693ae624ade32fd22d4e43c1,
  `Mathlib/Analysis/Analytic/Order.lean`, especially
  `analyticOrderAt_comp_of_deriv_ne_zero`, `analyticOrderAt_mul`, and the
  canonical `analyticOrderNatAt` definition.
* anthropics/formal-math
  @ fbdc36bbf17d20af3fd0447c6d1a8a02773c9844,
  `zeta23/Zeta23/ThmE/LocalCountChi.lean`, declaration
  `analyticOrderNatAt_gfunL`, and the analogous Riemann-zeta local-count code.

The formal-math declaration is specialized to Dirichlet L-functions.  The
mathematical content is entirely neutral: a nondegenerate affine change of
variable and multiplication by a nonzero constant preserve zero
multiplicity.  This module records exactly that neutral seam against the
currently pinned mathlib, so consumers need not duplicate the same proof.
-/

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic

namespace AnalyticNumberTheory.ComplexAnalysis

/-- A nondegenerate affine change of variable and multiplication by a nonzero
constant preserve the finite analytic zero multiplicity.

The function `f` only needs to be analytic at the affine image of the point;
there is no number-theoretic hypothesis in this statement. -/
theorem analyticOrderNatAt_affine_mul_const
    {f : ℂ → ℂ} {c κ u w : ℂ}
    (hf : AnalyticAt ℂ f (c + κ * w)) (hκ0 : κ ≠ 0) (hu0 : u ≠ 0) :
    analyticOrderNatAt (fun z : ℂ => f (c + κ * z) * u) w =
      analyticOrderNatAt f (c + κ * w) := by
  unfold analyticOrderNatAt
  congr 1
  have haff : AnalyticAt ℂ (fun z : ℂ => c + κ * z) w := by
    fun_prop
  have hcomp : AnalyticAt ℂ (fun z : ℂ => f (c + κ * z)) w :=
    hf.comp_of_eq haff rfl
  have hmul : (fun z : ℂ => f (c + κ * z) * u) =
      (fun z : ℂ => f (c + κ * z)) * fun _ : ℂ => u := rfl
  rw [hmul, analyticOrderAt_mul hcomp analyticAt_const]
  have hconst : analyticOrderAt (fun _ : ℂ => u) w = 0 :=
    analyticAt_const.analyticOrderAt_eq_zero.mpr hu0
  rw [hconst, add_zero]
  have hderiv : deriv (fun z : ℂ => c + κ * z) w ≠ 0 := by
    rw [deriv_const_add, deriv_const_mul _ differentiableAt_id, deriv_id'']
    simpa using hκ0
  have horder := analyticOrderAt_comp_of_deriv_ne_zero
    (f := f) haff hderiv
  simpa [Function.comp_def] using horder

end AnalyticNumberTheory.ComplexAnalysis
