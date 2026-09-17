import AnalyticNumberTheory.Dirichlet.ConditionalValueSeries

/-!
# Elementary growth bound for nonprincipal Dirichlet L-functions

This module extracts the minimal project-neutral growth estimate needed by the
existing finite-rectangle logarithmic-derivative formalization.

Provenance: adapted from
`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`,
`MathlibNt/AnalyticNumberTheory/DirichletL/DirichletLZeroFreeHalfPlaneLogDerivative.lean`.
The source and ANT use the same pinned mathlib revision
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

The conditional value-series infrastructure is reused from
`AnalyticNumberTheory.Dirichlet.ConditionalValueSeries`; no second
conditional-series framework is introduced here.
-/

open Complex

namespace AnalyticNumberTheory.Dirichlet

noncomputable section

/-- Elementary height-unrestricted growth of a nonprincipal Dirichlet
`L`-function on the half-plane `re z > 0`.

The estimate is obtained by specializing the explicit Abel tail at `m = 1`
and then identifying the naturally ordered conditional series with the actual
Mathlib `DirichletCharacter.LFunction`.
-/
theorem norm_LFunction_le_growth {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (z : ℂ) (hz : 0 < z.re) :
    ‖χ.LFunction z‖ ≤ q * (1 + ‖z‖ / z.re) := by
  have hq1 : q ≠ 1 := by
    intro h
    subst q
    exact hχ (Subsingleton.elim _ _)
  let : Fact (1 < q) :=
    ⟨Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨NeZero.ne q, hq1⟩⟩
  have hzero : χ (0 : ZMod q) = 0 :=
    MulChar.map_nonunit χ not_isUnit_zero
  have h := norm_orderedValueSeries_sub_sum_range_le
    χ hχ z hz (m := 1) le_rfl
  rw [orderedValueSeries_eq_LFunction_of_re_pos χ hχ z hz] at h
  simpa [hzero] using h

end AnalyticNumberTheory.Dirichlet
