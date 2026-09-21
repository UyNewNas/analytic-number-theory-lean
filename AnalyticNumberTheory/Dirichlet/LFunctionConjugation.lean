import AnalyticNumberTheory.Dirichlet.CompletedReflection
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Complex conjugation for analytically continued Dirichlet L-functions

Project-neutral minimal adaptation of the conjugation seam from
`subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`,
`BombieriVinogradov/Helpers/DirichletCharacter/ComplexConjugation.lean` and
`BombieriVinogradov/Proof/SiegelWalfisz/ZeroFree/LFunctionConjugation.lean`.

The source is on the same pinned Mathlib revision.  We retain only the coefficient/L-series
conjugation identities and the analytically continued ordinary-L identity.  No zero-count,
selected-height, completed-zero, GRH, contour, or application-specific statement is imported.
-/

set_option autoImplicit false

open scoped ComplexConjugate

namespace AnalyticNumberTheory.Dirichlet

/-- Complex conjugation of a complex Dirichlet-character value equals evaluation of the inverse
character. -/
theorem conj_apply_eq_inv_apply
    {N : Nat} (χ : DirichletCharacter Complex N) (a : ZMod N) :
    conj (χ a) = χ⁻¹ a := by
  simpa [RCLike.star_def] using MulChar.star_apply' χ a

/-- Conjugating the complex power of a natural number at the conjugate exponent restores the
original exponent. -/
theorem conj_natCast_cpow_conj (n : Nat) (s : Complex) :
    conj ((n : Complex) ^ conj s) = (n : Complex) ^ s := by
  have hArg : Complex.arg (n : Complex) ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_ne_zero.symm
  simpa using congrArg conj (Complex.cpow_conj (n : Complex) s hArg)

/-- Schwarz conjugation for the naive Dirichlet L-series. -/
theorem conj_LSeries_conj_eq_inv_LSeries
    {N : Nat} (χ : DirichletCharacter Complex N) (s : Complex) :
    conj (LSeries (χ ·) (conj s)) = LSeries (χ⁻¹ ·) s := by
  rw [LSeries, LSeries, RCLike.conj_tsum]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    rw [map_div₀ (starRingEnd Complex),
      conj_apply_eq_inv_apply,
      conj_natCast_cpow_conj]

/-- Schwarz conjugation for the analytically continued nonprincipal Dirichlet L-function:
`L(s, χ⁻¹) = conj (L(conj s, χ))`. -/
theorem LFunction_inv_eq_conj_conj
    {N : Nat} [NeZero N] {χ : DirichletCharacter Complex N}
    (hχ : χ ≠ 1) (s : Complex) :
    χ⁻¹.LFunction s = conj (χ.LFunction (conj s)) := by
  have hInverseNe : χ⁻¹ ≠ 1 := inv_ne_one_of_ne_one hχ
  let g : Complex → Complex := conj ∘ χ.LFunction ∘ conj
  have hDifferentiableG : Differentiable Complex g := by
    intro z
    have hAtConj : DifferentiableAt Complex χ.LFunction (conj z) :=
      (χ.differentiable_LFunction hχ).differentiableAt
    simpa [g] using hAtConj.conj_conj
  have hAnalyticInv :
      AnalyticOnNhd Complex χ⁻¹.LFunction (Set.univ : Set Complex) :=
    (χ⁻¹.differentiable_LFunction hInverseNe).differentiableOn.analyticOnNhd isOpen_univ
  have hAnalyticG : AnalyticOnNhd Complex g (Set.univ : Set Complex) :=
    hDifferentiableG.differentiableOn.analyticOnNhd isOpen_univ
  have hRightHalfPlane : {z : Complex | 1 < z.re} ∈ nhds (2 : Complex) :=
    (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num)
  have hEventually : χ⁻¹.LFunction =ᶠ[nhds (2 : Complex)] g := by
    filter_upwards [hRightHalfPlane] with z hz
    have hzConj : 1 < (conj z).re := by simpa using hz
    change χ⁻¹.LFunction z = conj (χ.LFunction (conj z))
    rw [χ⁻¹.LFunction_eq_LSeries hz,
      χ.LFunction_eq_LSeries hzConj]
    exact (conj_LSeries_conj_eq_inv_LSeries χ z).symm
  have hFunctions : χ⁻¹.LFunction = g :=
    AnalyticOnNhd.eq_of_eventuallyEq hAnalyticInv hAnalyticG hEventually
  simpa [g] using congrFun hFunctions s

end AnalyticNumberTheory.Dirichlet
