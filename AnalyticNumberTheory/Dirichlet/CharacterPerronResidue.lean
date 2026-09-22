import AnalyticNumberTheory.Dirichlet.CharacterPerron
import AnalyticNumberTheory.ComplexAnalysis.LogDerivResidue
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Real-endpoint residue for the sharp character Perron integrand

This module adds the local residue seam needed by consumers that keep the
nonintegral real Perron endpoint all the way through the contour shift.  It does
not add a contour theorem, zero-count input, GRH facade, or application-specific
parameter choice.
-/

open Complex

noncomputable section

namespace AnalyticNumberTheory.Dirichlet

/-- At every nonzero point, the residue of the real-endpoint character Perron
integrand is the analytic multiplicity times `-x^ρ / ρ`.  The endpoint remains
real, matching `characterPerronIntegrand` and avoiding any transport to a nearby
integer before the contour shift. -/
theorem residue_characterPerronIntegrand
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ : ρ ≠ 0) :
    residue (characterPerronIntegrand χ x) ρ =
      -((analyticOrderNatAt χ.LFunction ρ : ℕ) : ℂ) * ((x : ℂ) ^ ρ / ρ) := by
  have hAnalyticAll : ∀ z : ℂ, AnalyticAt ℂ χ.LFunction z :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt
  have hLFunctionNeZero : χ.LFunction ≠ 0 := by
    intro hzero
    have hone : χ.LFunction 1 = 0 := by
      simpa using congrFun hzero 1
    exact DirichletCharacter.LFunction_apply_one_ne_zero hχ hone
  have hOrderFinite : analyticOrderAt χ.LFunction ρ ≠ (⊤ : ENat) := by
    intro hTop
    exact hLFunctionNeZero
      ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ hAnalyticAll).mp hTop)
  let n : ℤ := analyticOrderNatAt χ.LFunction ρ
  have hOrder : meromorphicOrderAt χ.LFunction ρ = (n : WithTop ℤ) := by
    rw [(hAnalyticAll ρ).meromorphicOrderAt_eq]
    rw [← Nat.cast_analyticOrderNatAt hOrderFinite]
    simp [n]
  have hxne : x ≠ 0 := ne_of_gt hx
  have hxComplex : (x : ℂ) ≠ 0 := by
    exact_mod_cast hxne
  have hxCpow : ContinuousAt (fun s : ℂ => (x : ℂ) ^ s) ρ :=
    (differentiable_id.const_cpow (Or.inl hxComplex)).continuous.continuousAt
  have hCofactor : ContinuousAt (fun s : ℂ => -((x : ℂ) ^ s / s)) ρ :=
    (hxCpow.div continuousAt_id hρ).neg
  have hPrincipal :=
    AnalyticNumberTheory.ComplexAnalysis.logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt
      (hAnalyticAll ρ).meromorphicAt hOrder
  have hResidue :=
    AnalyticNumberTheory.ComplexAnalysis.residue_mul_eq_of_sub_principal_isBigO_one
      hPrincipal hCofactor
  have hfun :
      characterPerronIntegrand χ x =
        fun z => logDeriv χ.LFunction z * (-((x : ℂ) ^ z / z)) := by
    funext z
    simp [characterPerronIntegrand]
  rw [hfun]
  simpa [n] using hResidue

end AnalyticNumberTheory.Dirichlet
