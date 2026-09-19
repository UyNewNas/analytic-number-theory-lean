import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Symmetric completed Dirichlet-L reflection

Project-neutral extraction/adaptation of the completed-L reflection core used in
`subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`,
notably the source modules `CompletedNormalization`, `CompletedFunctionalEquation`,
`CompletedLogDerivativeReflection`, `NormalizationLogDerivative`,
`CompletedRegularLogDerivative`, and the primitive inverse/root-number helpers.

The source is on the same pinned Mathlib revision.  This module removes the
Siegel--Walfisz-specific lower-strip zero classification and exposes only the neutral
functional-equation/logarithmic-derivative identities under explicit regularity and
nonvanishing hypotheses.
-/

set_option autoImplicit false

namespace AnalyticNumberTheory.Dirichlet

/-- Inversion preserves nonprincipality for complex Dirichlet characters. -/
theorem inv_ne_one_of_ne_one
    {N : Nat} {χ : DirichletCharacter Complex N}
    (hχ : χ ≠ 1) : χ⁻¹ ≠ 1 := by
  intro hInverse
  apply hχ
  calc
    χ = (χ⁻¹)⁻¹ := by simp
    _ = (1 : DirichletCharacter Complex N)⁻¹ := congrArg Inv.inv hInverse
    _ = 1 := by simp

/-- Inversion preserves primitivity. -/
theorem primitive_inv
    {N : Nat} {χ : DirichletCharacter Complex N}
    (hPrimitive : DirichletCharacter.IsPrimitive χ) :
    DirichletCharacter.IsPrimitive χ⁻¹ := by
  rw [DirichletCharacter.IsPrimitive,
    DirichletCharacter.conductor_inv, hPrimitive]

/-- The standard Gauss sum of a primitive complex Dirichlet character is nonzero. -/
theorem primitive_gaussSum_stdAddChar_ne_zero
    {N : Nat} [NeZero N] {χ : DirichletCharacter Complex N}
    (hPrimitive : DirichletCharacter.IsPrimitive χ) :
    gaussSum χ ZMod.stdAddChar ≠ 0 := by
  intro hGauss
  have hFourierZero : ZMod.dft (fun x : ZMod N => χ x) = 0 := by
    funext k
    rw [hPrimitive.fourierTransform_eq_inv_mul_gaussSum, hGauss, mul_zero]
    rfl
  have hDouble := ZMod.dft_dft (fun x : ZMod N => χ x)
  rw [hFourierZero] at hDouble
  have hAt := congrFun hDouble (-1 : ZMod N)
  have hNCast : (N : Complex) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hZero : (N : Complex) = 0 := by
    simpa using hAt.symm
  exact hNCast hZero

/-- A primitive complex Dirichlet character has nonzero root number. -/
theorem primitive_rootNumber_ne_zero
    {N : Nat} [NeZero N] {χ : DirichletCharacter Complex N}
    (hPrimitive : DirichletCharacter.IsPrimitive χ) :
    χ.rootNumber ≠ 0 := by
  have hNCast : (N : Complex) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hNCpow : (N : Complex) ^ (1 / 2 : Complex) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (.inl hNCast)
  rw [DirichletCharacter.rootNumber]
  exact div_ne_zero
    (div_ne_zero (primitive_gaussSum_stdAddChar_ne_zero hPrimitive)
      (pow_ne_zero _ Complex.I_ne_zero))
    hNCpow

/-- Symmetric normalization of the completed Dirichlet L-function. -/
noncomputable def symmetricCompletedLFunction {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  (N : ℂ) ^ (s / 2) * χ.completedLFunction s

/-- The symmetric completion is entire for a nonprincipal character. -/
theorem differentiable_symmetricCompletedLFunction {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (symmetricCompletedLFunction χ) := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hpower : Differentiable ℂ (fun s : ℂ ↦ (N : ℂ) ^ (s / 2)) :=
    (differentiable_id.div_const 2).const_cpow (.inl hN)
  exact hpower.mul (χ.differentiable_completedLFunction hχ)

/-- Primitive functional equation in the symmetric normalization. -/
theorem symmetricCompletedLFunction_one_sub {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hPrimitive : DirichletCharacter.IsPrimitive χ)
    (s : ℂ) :
    symmetricCompletedLFunction χ (1 - s) =
      χ.rootNumber * symmetricCompletedLFunction χ⁻¹ s := by
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hpower :
      (N : ℂ) ^ ((1 - s) / 2) * (N : ℂ) ^ (s - 1 / 2) =
        (N : ℂ) ^ (s / 2) := by
    rw [← Complex.cpow_add _ _ hN]
    congr 1
    ring
  rw [symmetricCompletedLFunction,
    hPrimitive.completedLFunction_one_sub]
  change (N : ℂ) ^ ((1 - s) / 2) *
      ((N : ℂ) ^ (s - 1 / 2) * χ.rootNumber *
        χ⁻¹.completedLFunction s) =
    χ.rootNumber *
      ((N : ℂ) ^ (s / 2) * χ⁻¹.completedLFunction s)
  calc
    (N : ℂ) ^ ((1 - s) / 2) *
        ((N : ℂ) ^ (s - 1 / 2) * χ.rootNumber *
          χ⁻¹.completedLFunction s) =
      ((N : ℂ) ^ ((1 - s) / 2) *
        (N : ℂ) ^ (s - 1 / 2)) * χ.rootNumber *
          χ⁻¹.completedLFunction s := by ring
    _ = (N : ℂ) ^ (s / 2) * χ.rootNumber *
          χ⁻¹.completedLFunction s := by rw [hpower]
    _ = χ.rootNumber *
        ((N : ℂ) ^ (s / 2) * χ⁻¹.completedLFunction s) := by ring

/-- Reflection of the logarithmic derivative of the symmetric completion. -/
theorem logDeriv_symmetricCompletedLFunction_one_sub
    {N : Nat} [NeZero N] {χ : DirichletCharacter Complex N}
    (hχ : χ ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive χ)
    (s : Complex) :
    logDeriv (symmetricCompletedLFunction χ) (1 - s) =
      -logDeriv (symmetricCompletedLFunction χ⁻¹) s := by
  have hFunction :
      (fun w : Complex => symmetricCompletedLFunction χ (1 - w)) =
        fun w : Complex =>
          χ.rootNumber * symmetricCompletedLFunction χ⁻¹ w := by
    funext w
    exact symmetricCompletedLFunction_one_sub hPrimitive w
  have hLeft :
      logDeriv (fun w : Complex => symmetricCompletedLFunction χ (1 - w)) s =
        -logDeriv (symmetricCompletedLFunction χ) (1 - s) := by
    have hComp := logDeriv_comp
      (f := symmetricCompletedLFunction χ)
      (g := fun w : Complex => 1 - w)
      (x := s)
      ((differentiable_symmetricCompletedLFunction hχ).differentiableAt)
      (by fun_prop)
    simpa [Function.comp_def] using hComp
  have hRight :
      logDeriv
          (fun w : Complex =>
            χ.rootNumber * symmetricCompletedLFunction χ⁻¹ w) s =
        logDeriv (symmetricCompletedLFunction χ⁻¹) s :=
    logDeriv_const_mul s χ.rootNumber
      (primitive_rootNumber_ne_zero hPrimitive)
  have hLogDerivEquality :
      logDeriv (fun w : Complex => symmetricCompletedLFunction χ (1 - w)) s =
        logDeriv
          (fun w : Complex =>
            χ.rootNumber * symmetricCompletedLFunction χ⁻¹ w) s :=
    congrArg (fun f : Complex -> Complex => logDeriv f s) hFunction
  calc
    logDeriv (symmetricCompletedLFunction χ) (1 - s) =
        -logDeriv
          (fun w : Complex => symmetricCompletedLFunction χ (1 - w)) s := by
      rw [hLeft]
      ring
    _ = -logDeriv
          (fun w : Complex =>
            χ.rootNumber * symmetricCompletedLFunction χ⁻¹ w) s := by
      rw [hLogDerivEquality]
    _ = -logDeriv (symmetricCompletedLFunction χ⁻¹) s := by
      rw [hRight]

/-- Logarithmic derivative of the modulus normalization `N^(s/2)`. -/
theorem logDeriv_symmetricNormalization
    {N : Nat} [NeZero N] (s : Complex) :
    logDeriv (fun z : Complex => (N : Complex) ^ (z / 2)) s =
      (Real.log N : Complex) / 2 := by
  have hN : (N : Complex) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  rw [logDeriv_apply,
    Complex.deriv_const_cpow (f := fun z : Complex => z / 2) (by fun_prop)]
  simp [hN, Complex.natCast_log]
  ring

/-- Three-factor logarithmic-derivative identity at any regular nonzero point. -/
theorem logDeriv_symmetricCompletedLFunction_eq_three_factors_of_regular
    {N : Nat} [NeZero N] {χ : DirichletCharacter Complex N}
    (hχ : χ ≠ 1) {s : Complex}
    (hLFunctionNe : χ.LFunction s ≠ 0)
    (hGammaNe : χ.gammaFactor s ≠ 0)
    (hGammaDifferentiable : DifferentiableAt Complex χ.gammaFactor s) :
    logDeriv (symmetricCompletedLFunction χ) s =
      (Real.log N : Complex) / 2 +
        (logDeriv χ.LFunction s + logDeriv χ.gammaFactor s) := by
  have hNNeOne : N ≠ 1 := by
    intro hN
    exact hχ (χ.level_one' hN)
  have hCompletedValue :=
    χ.LFunction_eq_completed_div_gammaFactor s (Or.inr hNNeOne)
  have hCompletedNe : χ.completedLFunction s ≠ 0 := by
    intro hCompletedZero
    apply hLFunctionNe
    rw [hCompletedValue, hCompletedZero]
    simp
  have hCompletedDifferentiable :
      DifferentiableAt Complex χ.completedLFunction s :=
    (χ.differentiable_completedLFunction hχ).differentiableAt
  have hLFunctionAsQuotient :
      χ.LFunction = fun z : Complex =>
        χ.completedLFunction z / χ.gammaFactor z := by
    funext z
    exact χ.LFunction_eq_completed_div_gammaFactor z (Or.inr hNNeOne)
  have hLFunctionLogDerivative :
      logDeriv χ.LFunction s =
        logDeriv χ.completedLFunction s -
          logDeriv χ.gammaFactor s := by
    rw [hLFunctionAsQuotient]
    exact logDeriv_div s hCompletedNe hGammaNe
      hCompletedDifferentiable hGammaDifferentiable
  have hNCast : (N : Complex) ≠ 0 := by
    norm_num [NeZero.ne N]
  have hNormalizationNe :
      (N : Complex) ^ (s / 2) ≠ 0 := by
    simp [hNCast]
  have hNormalizationDifferentiable :
      DifferentiableAt Complex
        (fun z : Complex => (N : Complex) ^ (z / 2)) s :=
    ((differentiable_id.div_const (2 : Complex)).const_cpow
      (.inl hNCast)).differentiableAt
  have hOuter :=
    logDeriv_mul s hNormalizationNe hCompletedNe
      hNormalizationDifferentiable hCompletedDifferentiable
  calc
    logDeriv (symmetricCompletedLFunction χ) s =
        logDeriv (fun z : Complex => (N : Complex) ^ (z / 2)) s +
          logDeriv χ.completedLFunction s := by
      exact hOuter
    _ = (Real.log N : Complex) / 2 +
        logDeriv χ.completedLFunction s := by
      rw [logDeriv_symmetricNormalization]
    _ = (Real.log N : Complex) / 2 +
        (logDeriv χ.LFunction s + logDeriv χ.gammaFactor s) := by
      rw [hLFunctionLogDerivative]
      ring

/-- Exact ordinary-L logarithmic-derivative reflection at any pair of regular nonzero points.
This is the neutral identity needed by GRH consumers on lines such as `Re s = 1/4`; unlike the
source's left-line specialization it does not import a lower-strip zero classification. -/
theorem logDeriv_LFunction_eq_reflected_of_regular
    {N : Nat} [NeZero N] {χ : DirichletCharacter Complex N}
    (hχ : χ ≠ 1) (hPrimitive : DirichletCharacter.IsPrimitive χ)
    {s : Complex}
    (hLFunctionNe : χ.LFunction s ≠ 0)
    (hGammaNe : χ.gammaFactor s ≠ 0)
    (hGammaDifferentiable : DifferentiableAt Complex χ.gammaFactor s)
    (hInvLFunctionNe : χ⁻¹.LFunction (1 - s) ≠ 0)
    (hInvGammaNe : χ⁻¹.gammaFactor (1 - s) ≠ 0)
    (hInvGammaDifferentiable : DifferentiableAt Complex χ⁻¹.gammaFactor (1 - s)) :
    logDeriv χ.LFunction s =
      -(Real.log N : Complex) -
        logDeriv χ⁻¹.LFunction (1 - s) -
        logDeriv χ⁻¹.gammaFactor (1 - s) -
        logDeriv χ.gammaFactor s := by
  have hLeft :=
    logDeriv_symmetricCompletedLFunction_eq_three_factors_of_regular
      hχ hLFunctionNe hGammaNe hGammaDifferentiable
  have hInvNe : χ⁻¹ ≠ 1 := inv_ne_one_of_ne_one hχ
  have hRight :=
    logDeriv_symmetricCompletedLFunction_eq_three_factors_of_regular
      hInvNe hInvLFunctionNe hInvGammaNe hInvGammaDifferentiable
  have hReflectionRaw :=
    logDeriv_symmetricCompletedLFunction_one_sub hχ hPrimitive (1 - s)
  have hReflection :
      logDeriv (symmetricCompletedLFunction χ) s =
        -logDeriv (symmetricCompletedLFunction χ⁻¹) (1 - s) := by
    simpa using hReflectionRaw
  rw [hLeft, hRight] at hReflection
  linear_combination hReflection

end AnalyticNumberTheory.Dirichlet
