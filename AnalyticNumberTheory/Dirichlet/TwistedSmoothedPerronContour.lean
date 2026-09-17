import AnalyticNumberTheory.Dirichlet.TwistedSmoothedPerronHorizontal

/-!
# Finite contour identity for twisted smoothed Perron inversion

Provenance-preserving extraction of the character-neutral rectangle step used in
`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`, module
`MathlibNt/AnalyticNumberTheory/LargeSieve/DirichLTwistedSmoothedConductorLogEdges.lean`.

The external application packages its contour with a nonquadratic-character hypothesis.  The
actual rectangle identity does not need that arithmetic specialization: once holomorphy of the
Perron integrand on the rectangle is supplied by the caller, Cauchy's theorem gives the contour
shift for every character.  Downstream consumers can therefore obtain holomorphy from their own
zero-free/GRH input without duplicating rectangle-integration infrastructure.
-/

open Set Function Filter Complex Real MeasureTheory

namespace AnalyticNumberTheory.Dirichlet

variable {q : ℕ} [NeZero q]

/-- The complete twisted smoothed Perron integral around a finite rectangle vanishes whenever the
integrand is holomorphic on that rectangle.  This theorem is deliberately arithmetic-neutral. -/
theorem twistedSmoothedPerron_rectangleIntegral_eq_zero_of_holomorphicOn
    (χ : DirichletCharacter ℂ q) {ν : ℝ → ℝ} {ε X a b T : ℝ}
    (holo : HolomorphicOn (twistedSmoothedPerronIntegrand χ ν ε X)
      (((a : ℂ) - I * T).Rectangle (b + I * T))) :
    RectangleIntegral (twistedSmoothedPerronIntegrand χ ν ε X)
      ((a : ℂ) - I * T) (b + I * T) = 0 :=
  holo.vanishesOnRectangle (by rfl)

/-- Character-neutral finite contour shift.  The right finite vertical segment minus the left
finite vertical segment equals the upper horizontal edge minus the lower horizontal edge.

No GRH, zero-free region, character type, or smoothing regularity assumption appears here beyond
the caller-supplied holomorphy of the complete Perron integrand on the rectangle. -/
theorem twistedSmoothedPerron_finiteContourIdentity_of_holomorphicOn
    (χ : DirichletCharacter ℂ q) {ν : ℝ → ℝ} {ε X a b T : ℝ}
    (holo : HolomorphicOn (twistedSmoothedPerronIntegrand χ ν ε X)
      (((a : ℂ) - I * T).Rectangle (b + I * T))) :
    VIntegral (twistedSmoothedPerronIntegrand χ ν ε X) b (-T) T -
      VIntegral (twistedSmoothedPerronIntegrand χ ν ε X) a (-T) T =
      HIntegral (twistedSmoothedPerronIntegrand χ ν ε X) a b T -
      HIntegral (twistedSmoothedPerronIntegrand χ ν ε X) a b (-T) := by
  have hz := twistedSmoothedPerron_rectangleIntegral_eq_zero_of_holomorphicOn χ holo
  norm_num [RectangleIntegral] at hz
  linear_combination hz

end AnalyticNumberTheory.Dirichlet
