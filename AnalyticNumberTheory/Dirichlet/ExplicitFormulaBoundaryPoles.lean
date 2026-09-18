import AnalyticNumberTheory.Dirichlet.ExplicitFormulaResidue
import AnalyticNumberTheory.Dirichlet.ExplicitFormulaDyadicOrigin
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.FunProp
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles

/-!
# Boundary-pole control for the Dirichlet explicit-formula integrand

This module source-adapts the smallest project-neutral boundary seam from
`subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`:

* `.../Residue/Poles/OriginalPoleZero.lean`;
* `.../Residue/Poles/BoundaryDisjoint.lean`.

It classifies every nonzero pole of the unregularized nonprincipal
Dirichlet explicit-formula integrand as an actual zero of the Dirichlet
`L`-function, then converts pointwise boundary nonvanishing plus exclusion of
`0` into the `Disjoint` pole-boundary hypothesis expected by the existing
rectangle residue theorem.

For the already-integrated sharp dyadic endpoint difference, the removable
origin kernel makes the corresponding boundary theorem stronger: no separate
assumption that the border avoids `0` is needed.  That dyadic corollary is a
thin composition of the verified ANT origin-cancellation theorem with the same
analytic-order argument; it does not import the heavier Liu--Wang regularized
single-endpoint contour hierarchy.

No zero-free region, good-height existence theorem, GRH consequence, residue
sum, or downstream parameter choice is asserted here.
-/

open Complex

noncomputable section

namespace AnalyticNumberTheory.Dirichlet

/-- Away from the separate Perron-kernel point `0`, every pole of the
nonprincipal Dirichlet explicit-formula integrand comes from a zero of the
Dirichlet `L`-function. -/
theorem LFunction_eq_zero_of_explicitFormulaIntegrand_pole
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (x : ℕ) (hx : 0 < x)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hpole : meromorphicOrderAt (explicitFormulaIntegrand χ x) ρ < 0) :
    χ.LFunction ρ = 0 := by
  by_contra hLNe
  have hLAnalytic : AnalyticAt ℂ χ.LFunction ρ :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt ρ
  have hLogAnalytic : AnalyticAt ℂ (logDeriv χ.LFunction) ρ := by
    unfold logDeriv
    exact hLAnalytic.deriv.div hLAnalytic hLNe
  have hxC : (x : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hx
  have hPowAnalytic : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s) ρ := by
    simp_rw [Complex.cpow_def_of_ne_zero hxC]
    fun_prop
  have hKernelAnalytic :
      AnalyticAt ℂ (fun s : ℂ => -((x : ℂ) ^ s / s)) ρ :=
    (hPowAnalytic.div (by fun_prop) hρ).neg
  have hOriginalAnalytic : AnalyticAt ℂ (explicitFormulaIntegrand χ x) ρ := by
    unfold explicitFormulaIntegrand
    exact hLogAnalytic.mul hKernelAnalytic
  exact (not_lt_of_ge hOriginalAnalytic.meromorphicOrderAt_nonneg) hpole

/-- If the rectangle border avoids `0` and the Dirichlet `L`-function is
nonzero at every boundary point, then the unregularized explicit-formula
integrand has no pole on that border. -/
theorem disjoint_explicitFormulaIntegrand_poles_boundary_of_LFunction_ne_zero
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (x : ℕ) (hx : 0 < x) (z w : ℂ)
    (hzero : ¬ (RectangleBorder z w) 0)
    (hLFunction : ∀ p : ℂ, (RectangleBorder z w) p → χ.LFunction p ≠ 0) :
    Disjoint (RectangleBorder z w)
      {p | meromorphicOrderAt (explicitFormulaIntegrand χ x) p < 0} := by
  rw [Set.disjoint_left]
  intro p hpBorder hpPole
  have hpNe : p ≠ 0 := by
    intro hpZero
    apply hzero
    change (RectangleBorder z w) p at hpBorder
    rw [hpZero] at hpBorder
    exact hpBorder
  have hLZero : χ.LFunction p = 0 :=
    LFunction_eq_zero_of_explicitFormulaIntegrand_pole hχ x hx hpNe hpPole
  exact (hLFunction p hpBorder) hLZero

/-- Every pole of the origin-cancelled sharp dyadic endpoint difference comes
from an actual zero of the nonprincipal Dirichlet `L`-function.  Unlike the
single-endpoint statement above, this includes `ρ = 0`: the dyadic Perron
kernel is meromorphic with nonnegative order there, so it contributes no pole. -/
theorem LFunction_eq_zero_of_explicitFormulaDyadicIntegrand_pole
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (P : ℕ) (hP : 0 < P)
    {ρ : ℂ}
    (hpole : meromorphicOrderAt (explicitFormulaDyadicIntegrand χ P) ρ < 0) :
    χ.LFunction ρ = 0 := by
  by_contra hLNe
  have hLAnalytic : AnalyticAt ℂ χ.LFunction ρ :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt ρ
  have hLogAnalytic : AnalyticAt ℂ (logDeriv χ.LFunction) ρ := by
    unfold logDeriv
    exact hLAnalytic.deriv.div hLAnalytic hLNe
  have hKernelMero := meromorphic_explicitFormulaDyadicOriginKernel P hP
  have hKernelOrder :=
    meromorphicOrderAt_explicitFormulaDyadicOriginKernel_nonneg P hP ρ
  have hFactor :
      explicitFormulaDyadicIntegrand χ P =
        -(logDeriv χ.LFunction * explicitFormulaDyadicOriginKernel P) := by
    funext s
    exact explicitFormulaDyadicIntegrand_eq_neg_logDeriv_mul_originKernel χ P s
  rw [hFactor,
    Eq.symm (meromorphicOrderAt_neg
      (x := ρ) (f := logDeriv χ.LFunction * explicitFormulaDyadicOriginKernel P)),
    meromorphicOrderAt_mul hLogAnalytic.meromorphicAt (hKernelMero ρ)] at hpole
  exact (not_lt_of_ge
    (add_nonneg hLogAnalytic.meromorphicOrderAt_nonneg hKernelOrder)) hpole

/-- Pointwise nonvanishing of the Dirichlet `L`-function on a rectangle border
already excludes every pole of the sharp dyadic endpoint difference.  No
separate `0 ∉ border` premise is necessary because the endpoint difference has
removed the Perron-kernel singularity at the origin. -/
theorem disjoint_explicitFormulaDyadicIntegrand_poles_boundary_of_LFunction_ne_zero
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (P : ℕ) (hP : 0 < P) (z w : ℂ)
    (hLFunction : ∀ p : ℂ, (RectangleBorder z w) p → χ.LFunction p ≠ 0) :
    Disjoint (RectangleBorder z w)
      {p | meromorphicOrderAt (explicitFormulaDyadicIntegrand χ P) p < 0} := by
  rw [Set.disjoint_left]
  intro p hpBorder hpPole
  have hLZero : χ.LFunction p = 0 :=
    LFunction_eq_zero_of_explicitFormulaDyadicIntegrand_pole hχ P hP hpPole
  exact (hLFunction p hpBorder) hLZero

end AnalyticNumberTheory.Dirichlet
