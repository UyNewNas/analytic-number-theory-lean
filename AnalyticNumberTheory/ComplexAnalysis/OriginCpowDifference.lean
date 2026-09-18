import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Positive-base complex-power difference quotient at the origin

This module is a bounded, project-neutral source adaptation of
`BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Residue/Origin/KernelDifference.lean`
from `subfish-zhou/liu-wang-ternary-goldbach-lean` at commit
`b57b7307810c37267e47110d8b5f920e3e681c81` (source blob
`50471e9ffecd7a83e393bf5409da5302113f3d23`).  That repository uses the same
pinned Mathlib revision as ANT.

The declarations isolate the removable singularity of `((x^s) - 1) / s` at
`s = 0`.  They are independent of Dirichlet characters, GRH, explicit-formula
residues, and all downstream Mangerel/Liouville parameters.
-/

set_option autoImplicit false

noncomputable section

namespace AnalyticNumberTheory.ComplexAnalysis

/-- The difference quotient which removes the constant term of the positive-base
complex exponential at the origin. -/
def originCpowDifferenceQuotient (x : ℕ) (s : ℂ) : ℂ :=
  ((x : ℂ) ^ s - 1) / s

/-- For a positive natural base, the complex-power difference quotient is
meromorphic on the complex plane. -/
theorem meromorphic_originCpowDifferenceQuotient
    (x : ℕ) (hx : 0 < x) :
    Meromorphic (originCpowDifferenceQuotient x) := by
  have hxC : (x : ℂ) ≠ 0 := by
    exact_mod_cast hx.ne'
  intro s
  have hPow :
      AnalyticAt ℂ (fun z : ℂ => (x : ℂ) ^ z) s := by
    simp_rw [Complex.cpow_def_of_ne_zero hxC]
    fun_prop
  have hNum :
      MeromorphicAt (fun z : ℂ => (x : ℂ) ^ z - 1) s :=
    (hPow.sub (by fun_prop)).meromorphicAt
  have hDen : MeromorphicAt (fun z : ℂ => z) s := by
    fun_prop
  exact hNum.div hDen

/-- The punctured limit of `((x^s) - 1) / s` at the origin is `log x`. -/
theorem tendsto_originCpowDifferenceQuotient_zero
    (x : ℕ) (hx : 0 < x) :
    Filter.Tendsto (originCpowDifferenceQuotient x)
      (nhdsWithin 0 (Set.compl ({0} : Set ℂ)))
      (nhds (Complex.log (x : ℂ))) := by
  have hxC : (x : ℂ) ≠ 0 := by
    exact_mod_cast hx.ne'
  have hDeriv :
      HasDerivAt (fun z : ℂ => (x : ℂ) ^ z)
        (Complex.log (x : ℂ)) 0 := by
    simpa using
      (Complex.hasStrictDerivAt_const_cpow
        (x := (x : ℂ)) (y := (0 : ℂ)) (Or.inl hxC)).hasDerivAt
  have hFunction :
      originCpowDifferenceQuotient x =
        slope (fun z : ℂ => (x : ℂ) ^ z) 0 := by
    funext z
    simp [originCpowDifferenceQuotient, slope, smul_eq_mul, div_eq_mul_inv,
      mul_comm]
  rw [hFunction]
  exact hDeriv.tendsto_slope

/-- The removable complex-power difference quotient has nonnegative
meromorphic order at the origin. -/
theorem meromorphicOrderAt_originCpowDifferenceQuotient_zero_nonneg
    (x : ℕ) (hx : 0 < x) :
    0 ≤ meromorphicOrderAt (originCpowDifferenceQuotient x) 0 := by
  apply (tendsto_nhds_iff_meromorphicOrderAt_nonneg
    (meromorphic_originCpowDifferenceQuotient x hx 0)).mp
  exact ⟨Complex.log (x : ℂ), tendsto_originCpowDifferenceQuotient_zero x hx⟩

end AnalyticNumberTheory.ComplexAnalysis
