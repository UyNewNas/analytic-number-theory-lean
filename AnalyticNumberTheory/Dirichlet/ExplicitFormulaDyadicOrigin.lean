import AnalyticNumberTheory.Dirichlet.ExplicitFormulaResidue
import AnalyticNumberTheory.ComplexAnalysis.OriginCpowDifference

/-!
# Dyadic endpoint cancellation for the Dirichlet explicit-formula integrand

This neutral module isolates the algebraic cancellation at `s = 0` in the
difference between the explicit-formula endpoints `x = P` and `x = 2P`.

For a single endpoint, the Perron factor `x^s / s` can combine with a pole of
`L'/L` at the origin to create a double pole.  In the dyadic difference the
kernel factors as

`P^s * ((2^s - 1) / s)`,

and the quotient factor has a removable singularity at `0` by the same-pin
Liu--Wang result source-adapted in `OriginCpowDifference`.

No GRH, zero count, contour geometry, Mangerel parameter, or Liouville-specific
object appears here.
-/

set_option autoImplicit false

noncomputable section

open Complex

namespace AnalyticNumberTheory.Dirichlet

/-- Difference between the two natural endpoints of a dyadic explicit-formula
window. -/
def explicitFormulaDyadicIntegrand
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (P : ℕ) (s : ℂ) : ℂ :=
  explicitFormulaIntegrand χ (2 * P) s - explicitFormulaIntegrand χ P s

/-- The dyadic Perron kernel after cancelling the common origin singularity. -/
def explicitFormulaDyadicOriginKernel (P : ℕ) (s : ℂ) : ℂ :=
  (P : ℂ) ^ s *
    AnalyticNumberTheory.ComplexAnalysis.originCpowDifferenceQuotient 2 s

/-- Exact pointwise factorization of the dyadic endpoint difference through the
origin-regular kernel. -/
theorem explicitFormulaDyadicIntegrand_eq_neg_logDeriv_mul_originKernel
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (P : ℕ) (s : ℂ) :
    explicitFormulaDyadicIntegrand χ P s =
      -(logDeriv χ.LFunction s * explicitFormulaDyadicOriginKernel P s) := by
  unfold explicitFormulaDyadicIntegrand explicitFormulaIntegrand
    explicitFormulaDyadicOriginKernel
    AnalyticNumberTheory.ComplexAnalysis.originCpowDifferenceQuotient
  rw [Complex.natCast_mul_natCast_cpow 2 P s]
  ring

/-- For positive `P`, the origin-regular dyadic kernel is meromorphic on the
whole complex plane. -/
theorem meromorphic_explicitFormulaDyadicOriginKernel
    (P : ℕ) (hP : 0 < P) :
    Meromorphic (explicitFormulaDyadicOriginKernel P) := by
  have hPC : (P : ℂ) ≠ 0 := by
    exact_mod_cast hP.ne'
  have hPow : Meromorphic (fun s : ℂ => (P : ℂ) ^ s) := by
    intro s
    have hPowAn : AnalyticAt ℂ (fun z : ℂ => (P : ℂ) ^ z) s := by
      simp_rw [Complex.cpow_def_of_ne_zero hPC]
      fun_prop
    exact hPowAn.meromorphicAt
  exact hPow.mul
    (AnalyticNumberTheory.ComplexAnalysis.meromorphic_originCpowDifferenceQuotient
      2 (by norm_num))

/-- The dyadic kernel itself contributes no pole at the origin. -/
theorem meromorphicOrderAt_explicitFormulaDyadicOriginKernel_zero_nonneg
    (P : ℕ) (hP : 0 < P) :
    0 ≤ meromorphicOrderAt (explicitFormulaDyadicOriginKernel P) 0 := by
  have hPC : (P : ℂ) ≠ 0 := by
    exact_mod_cast hP.ne'
  have hPowAn : AnalyticAt ℂ (fun z : ℂ => (P : ℂ) ^ z) 0 := by
    simp_rw [Complex.cpow_def_of_ne_zero hPC]
    fun_prop
  have hQuotMero :=
    AnalyticNumberTheory.ComplexAnalysis.meromorphic_originCpowDifferenceQuotient
      2 (by norm_num)
  have hQuotOrder :=
    AnalyticNumberTheory.ComplexAnalysis.meromorphicOrderAt_originCpowDifferenceQuotient_zero_nonneg
      2 (by norm_num)
  unfold explicitFormulaDyadicOriginKernel
  rw [meromorphicOrderAt_mul hPowAn.meromorphicAt (hQuotMero 0)]
  exact add_nonneg hPowAn.meromorphicOrderAt_nonneg hQuotOrder

end AnalyticNumberTheory.Dirichlet
