import Mathlib.Analysis.Meromorphic.RCLike
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import AnalyticNumberTheory.ComplexAnalysis.LogDerivSimplePoles

/-!
# Simple poles of nonprincipal Dirichlet logarithmic derivatives

This module is a bounded, project-neutral source adaptation of the exact-same-pin
Liu--Wang explicit-formula pole infrastructure at
`subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`.

It exposes only the finite-order facts needed to conclude that the logarithmic
derivative of a nonprincipal Dirichlet L-function has at most simple poles on an
arbitrary set. No contour theorem, zero count, GRH consequence, endpoint kernel,
or downstream Mangerel/Liouville parameter is introduced.
-/

set_option autoImplicit false

noncomputable section

namespace AnalyticNumberTheory.Dirichlet

/-- A nonprincipal Dirichlet L-function is meromorphic on the complex plane. -/
theorem meromorphic_LFunction_of_ne_one
    {N : Nat} [NeZero N] {χ : DirichletCharacter Complex N}
    (hχ : χ ≠ 1) : Meromorphic χ.LFunction := by
  intro s
  exact ((DirichletCharacter.differentiable_LFunction hχ).analyticAt s).meromorphicAt

/-- The logarithmic derivative of a nonprincipal Dirichlet L-function is
meromorphic on the complex plane. -/
theorem meromorphic_logDeriv_LFunction
    {N : Nat} [NeZero N] {χ : DirichletCharacter Complex N}
    (hχ : χ ≠ 1) : Meromorphic (logDeriv χ.LFunction) := by
  apply Meromorphic.logDeriv
  intro s
  exact ((DirichletCharacter.differentiable_LFunction hχ).analyticAt s).meromorphicAt

/-- A nonprincipal Dirichlet L-function has finite meromorphic order at every
point of the complex plane. -/
theorem meromorphicOrderAt_LFunction_ne_top
    {N : Nat} [NeZero N] {χ : DirichletCharacter Complex N}
    (hχ : χ ≠ 1) (s : Complex) :
    meromorphicOrderAt χ.LFunction s ≠ (⊤ : WithTop Int) := by
  have hMero := meromorphic_LFunction_of_ne_one hχ
  apply (hMero.exists_meromorphicOrderAt_ne_top_iff_forall).mp
  refine ⟨(2 : Complex), ?_⟩
  apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hMero 2)).mpr
  have hValue : χ.LFunction (2 : Complex) ≠ 0 :=
    χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by norm_num)
  have hContinuous : ContinuousAt χ.LFunction (2 : Complex) :=
    (DirichletCharacter.differentiable_LFunction hχ).continuous.continuousAt
  exact (hContinuous.eventually_ne hValue).filter_mono inf_le_left

/-- The logarithmic derivative of a nonprincipal Dirichlet L-function has at
most simple poles on every set. Multiplicities of L-function zeros are carried
by the residues rather than by higher pole order of the logarithmic derivative. -/
theorem hasSimplePolesOn_logDeriv_LFunction
    {N : Nat} [NeZero N] {χ : DirichletCharacter Complex N}
    (hχ : χ ≠ 1) (U : Set Complex) :
    HasSimplePolesOn (logDeriv χ.LFunction) U :=
  AnalyticNumberTheory.ComplexAnalysis.logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top
    (meromorphic_LFunction_of_ne_one hχ).meromorphicOn
    (meromorphic_logDeriv_LFunction hχ).meromorphicOn
    (fun p _ => meromorphicOrderAt_LFunction_ne_top hχ p)

end AnalyticNumberTheory.Dirichlet
