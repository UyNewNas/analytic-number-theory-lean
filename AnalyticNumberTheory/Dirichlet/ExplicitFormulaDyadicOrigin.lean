import AnalyticNumberTheory.Dirichlet.ExplicitFormulaResidue
import AnalyticNumberTheory.Dirichlet.LogDerivativeSimplePoles
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
  rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow 2 P s]
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
  change 0 ≤ meromorphicOrderAt
    ((fun z : ℂ => (P : ℂ) ^ z) *
      AnalyticNumberTheory.ComplexAnalysis.originCpowDifferenceQuotient 2) 0
  rw [meromorphicOrderAt_mul hPowAn.meromorphicAt (hQuotMero 0)]
  exact add_nonneg hPowAn.meromorphicOrderAt_nonneg hQuotOrder

/-- For positive `P`, the origin-regular dyadic kernel has nonnegative
meromorphic order at every point. At zero this is the removable-singularity
result above; away from zero the quotient is analytic because its denominator
does not vanish. -/
theorem meromorphicOrderAt_explicitFormulaDyadicOriginKernel_nonneg
    (P : ℕ) (hP : 0 < P) (s : ℂ) :
    0 ≤ meromorphicOrderAt (explicitFormulaDyadicOriginKernel P) s := by
  by_cases hs : s = 0
  · subst s
    exact meromorphicOrderAt_explicitFormulaDyadicOriginKernel_zero_nonneg P hP
  · have hPC : (P : ℂ) ≠ 0 := by
      exact_mod_cast hP.ne'
    have hPowAn : AnalyticAt ℂ (fun z : ℂ => (P : ℂ) ^ z) s := by
      simp_rw [Complex.cpow_def_of_ne_zero hPC]
      fun_prop
    have hTwoC : (2 : ℂ) ≠ 0 := by norm_num
    have hTwoPowAn : AnalyticAt ℂ (fun z : ℂ => (2 : ℂ) ^ z) s := by
      simp_rw [Complex.cpow_def_of_ne_zero hTwoC]
      fun_prop
    have hQuotAn :
        AnalyticAt ℂ
          (AnalyticNumberTheory.ComplexAnalysis.originCpowDifferenceQuotient 2) s := by
      unfold AnalyticNumberTheory.ComplexAnalysis.originCpowDifferenceQuotient
      exact (hTwoPowAn.sub (by fun_prop)).div (by fun_prop) hs
    change 0 ≤ meromorphicOrderAt
      ((fun z : ℂ => (P : ℂ) ^ z) *
        AnalyticNumberTheory.ComplexAnalysis.originCpowDifferenceQuotient 2) s
    exact (hPowAn.mul hQuotAn).meromorphicOrderAt_nonneg

/-- For a nonprincipal character and positive dyadic scale, the complete sharp
dyadic explicit-formula integrand has at most simple poles on every set. -/
theorem hasSimplePolesOn_explicitFormulaDyadicIntegrand
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (P : ℕ) (hP : 0 < P) (U : Set ℂ) :
    HasSimplePolesOn (explicitFormulaDyadicIntegrand χ P) U := by
  have hLog := hasSimplePolesOn_logDeriv_LFunction hχ U
  have hLogMero := meromorphic_logDeriv_LFunction hχ
  have hKernelMero := meromorphic_explicitFormulaDyadicOriginKernel P hP
  intro s hs
  rw [show explicitFormulaDyadicIntegrand χ P =
      -(logDeriv χ.LFunction * explicitFormulaDyadicOriginKernel P) by
        funext z
        exact explicitFormulaDyadicIntegrand_eq_neg_logDeriv_mul_originKernel χ P z,
    Eq.symm (meromorphicOrderAt_neg
      (x := s) (f := logDeriv χ.LFunction * explicitFormulaDyadicOriginKernel P)),
    meromorphicOrderAt_mul (hLogMero s) (hKernelMero s)]
  simpa using add_le_add (hLog s hs)
    (meromorphicOrderAt_explicitFormulaDyadicOriginKernel_nonneg P hP s)

/-- Away from the removable origin, the residue of the sharp dyadic endpoint
difference is the analytic multiplicity times the origin-cancelled dyadic
kernel.  This is the direct local residue formula needed before reindexing a
finite contour residue sum. -/
theorem residue_explicitFormulaDyadicIntegrand
    {N P : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hP : 0 < P) {ρ : ℂ} (hρ : ρ ≠ 0) :
    residue (explicitFormulaDyadicIntegrand χ P) ρ =
      -((analyticOrderNatAt χ.LFunction ρ : ℕ) : ℂ) *
        explicitFormulaDyadicOriginKernel P ρ := by
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
  have hPrincipal :=
    AnalyticNumberTheory.ComplexAnalysis.logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt
      (hAnalyticAll ρ).meromorphicAt hOrder
  have hPC : (P : ℂ) ≠ 0 := by
    exact_mod_cast hP.ne'
  have hPowAn : AnalyticAt ℂ (fun z : ℂ => (P : ℂ) ^ z) ρ := by
    simp_rw [Complex.cpow_def_of_ne_zero hPC]
    fun_prop
  have hTwoC : (2 : ℂ) ≠ 0 := by norm_num
  have hTwoPowAn : AnalyticAt ℂ (fun z : ℂ => (2 : ℂ) ^ z) ρ := by
    simp_rw [Complex.cpow_def_of_ne_zero hTwoC]
    fun_prop
  have hQuotAn :
      AnalyticAt ℂ
        (AnalyticNumberTheory.ComplexAnalysis.originCpowDifferenceQuotient 2) ρ := by
    unfold AnalyticNumberTheory.ComplexAnalysis.originCpowDifferenceQuotient
    exact (hTwoPowAn.sub (by fun_prop)).div (by fun_prop) hρ
  have hKernelContinuous :
      ContinuousAt (fun z : ℂ => -explicitFormulaDyadicOriginKernel P z) ρ := by
    unfold explicitFormulaDyadicOriginKernel
    exact (hPowAn.mul hQuotAn).continuousAt.neg
  have hResidue :=
    AnalyticNumberTheory.ComplexAnalysis.residue_mul_eq_of_sub_principal_isBigO_one
      hPrincipal hKernelContinuous
  rw [show explicitFormulaDyadicIntegrand χ P =
      fun z => logDeriv χ.LFunction z * (-explicitFormulaDyadicOriginKernel P z) by
        funext z
        rw [explicitFormulaDyadicIntegrand_eq_neg_logDeriv_mul_originKernel]
        ring]
  simpa [n] using hResidue

/-- At every nonzero point, taking the residue of the direct dyadic integrand is
exactly the same as subtracting the two already-verified endpoint residues.
The statement is deliberately local: it does not assume or manufacture a
linearity law for the repository's simple-pole `residue` stopgap. -/
theorem residue_explicitFormulaDyadicIntegrand_eq_sub
    {N P : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hP : 0 < P) {ρ : ℂ} (hρ : ρ ≠ 0) :
    residue (explicitFormulaDyadicIntegrand χ P) ρ =
      residue (explicitFormulaIntegrand χ (2 * P)) ρ -
        residue (explicitFormulaIntegrand χ P) ρ := by
  rw [residue_explicitFormulaDyadicIntegrand hχ hP hρ,
    residue_explicitFormulaIntegrand hχ (Nat.mul_pos (by norm_num) hP) hρ,
    residue_explicitFormulaIntegrand hχ hP hρ]
  unfold explicitFormulaDyadicOriginKernel
    AnalyticNumberTheory.ComplexAnalysis.originCpowDifferenceQuotient
  rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow 2 P ρ]
  ring

end AnalyticNumberTheory.Dirichlet
