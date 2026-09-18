import AnalyticNumberTheory.ComplexAnalysis.LogDerivResidue
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# A Dirichlet-L explicit-formula residue atom

This module is the neutral Dirichlet-character specialization of the local residue
calculation used in a truncated explicit formula.  The source audit is
`subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`,
`BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/ZeroResidue.lean` and
`BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Residue/Meromorphic/{LFunction,Kernel,Main}.lean`.

Only the reusable meromorphicity and local residue calculations are adapted here.
No contour theorem, GRH input, Liouville defect, Mangerel parameter choice, or downstream
target is assumed.
-/

open Complex

noncomputable section

namespace AnalyticNumberTheory.Dirichlet

/-- The standard logarithmic-derivative integrand whose residues encode the
multiplicity-weighted `x^ρ / ρ` terms of a Dirichlet explicit formula. -/
def explicitFormulaIntegrand {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (x : ℕ) (s : ℂ) : ℂ :=
  logDeriv χ.LFunction s * (-((x : ℂ) ^ s / s))

/-- For a nonprincipal character and positive natural endpoint, the explicit-formula
integrand is meromorphic on the whole complex plane.  This is the neutral source-level
fact needed before applying any finite contour residue theorem. -/
theorem meromorphic_explicitFormulaIntegrand
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (x : ℕ) (hx : 0 < x) :
    Meromorphic (explicitFormulaIntegrand χ x) := by
  have hLog : Meromorphic (logDeriv χ.LFunction) := by
    apply Meromorphic.logDeriv
    intro s
    exact ((DirichletCharacter.differentiable_LFunction hχ).analyticAt s).meromorphicAt
  have hxC : (x : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hx
  have hPowDiff : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) :=
    differentiable_id.const_cpow (Or.inl hxC)
  have hPow : Meromorphic (fun s : ℂ => (x : ℂ) ^ s) := by
    intro s
    exact (hPowDiff.analyticAt s).meromorphicAt
  have hDenDiff : Differentiable ℂ (fun s : ℂ => s) := by
    fun_prop
  have hDen : Meromorphic (fun s : ℂ => s) := by
    intro s
    exact (hDenDiff.analyticAt s).meromorphicAt
  exact hLog.mul (hPow.div hDen).neg

/-- Set-restricted form of `meromorphic_explicitFormulaIntegrand`. -/
theorem meromorphicOn_explicitFormulaIntegrand
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (x : ℕ) (hx : 0 < x) (U : Set ℂ) :
    MeromorphicOn (explicitFormulaIntegrand χ x) U :=
  (meromorphic_explicitFormulaIntegrand hχ x hx).meromorphicOn

/-- At every nonzero point, the residue of the nonprincipal Dirichlet-L explicit-formula
integrand is the analytic multiplicity times `-x^ρ/ρ`.  When `ρ` is not a zero the
analytic order is zero, so the same formula remains valid. -/
theorem residue_explicitFormulaIntegrand
    {N x : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hx : 0 < x) {ρ : ℂ} (hρ : ρ ≠ 0) :
    residue (explicitFormulaIntegrand χ x) ρ =
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
  have hxComplex : (x : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hx
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
  change residue (fun z => logDeriv χ.LFunction z * (-((x : ℂ) ^ z / z))) ρ = _
  simpa [n] using hResidue

end AnalyticNumberTheory.Dirichlet
