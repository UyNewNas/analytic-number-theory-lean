import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Dirichlet gamma-factor regularity in the positive half-plane

Project-neutral extraction/adaptation of
`subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`,
`BombieriVinogradov/Proof/SiegelWalfisz/ZeroFree/GammaFactorRegularity.lean`.

The source is on the same pinned Mathlib revision.  These lemmas are exactly the regularity
facts needed to discharge the gamma-factor hypotheses in completed-L reflection arguments;
no zero-free region or application-specific assumption is involved.
-/

set_option autoImplicit false

namespace AnalyticNumberTheory.Dirichlet

/-- The real gamma factor is differentiable at every point of positive real part. -/
theorem differentiableAt_Gammaℝ_of_re_pos
    {s : Complex} (hs : 0 < s.re) :
    DifferentiableAt Complex Complex.Gammaℝ s := by
  unfold Complex.Gammaℝ
  apply DifferentiableAt.mul
  · exact ((differentiable_id.neg.div_const 2).const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).differentiableAt
  · apply (Complex.differentiableAt_Gamma (s / 2) ?_).comp s
      ((differentiable_id.div_const (2 : Complex)).differentiableAt)
    intro m hPole
    have hPositive : 0 < (s / 2).re := by
      rw [Complex.div_ofNat_re]
      exact div_pos hs (by norm_num)
    have hNonpositive : (s / 2).re ≤ 0 := by
      rw [hPole]
      simp
    linarith

/-- A Dirichlet character's parity-selected gamma factor is nonzero in `Re(s) > 0`. -/
theorem gammaFactor_ne_zero_of_re_pos
    {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex}
    (hs : 0 < s.re) : χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with hEven | hOdd
  · rw [hEven.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [hOdd.gammaFactor_def]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp
    linarith

/-- A Dirichlet character's parity-selected gamma factor is differentiable in `Re(s) > 0`. -/
theorem differentiableAt_gammaFactor_of_re_pos
    {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex}
    (hs : 0 < s.re) : DifferentiableAt Complex χ.gammaFactor s := by
  rcases χ.even_or_odd with hEven | hOdd
  · have hFunction : χ.gammaFactor = Complex.Gammaℝ := by
      funext z
      exact hEven.gammaFactor_def z
    rw [hFunction]
    exact differentiableAt_Gammaℝ_of_re_pos hs
  · have hFunction : χ.gammaFactor = fun z => Complex.Gammaℝ (z + 1) := by
      funext z
      exact hOdd.gammaFactor_def z
    rw [hFunction]
    apply (differentiableAt_Gammaℝ_of_re_pos (s := s + 1) ?_).comp s
      ((differentiable_id.add_const (1 : Complex)).differentiableAt)
    simp
    linarith

end AnalyticNumberTheory.Dirichlet
