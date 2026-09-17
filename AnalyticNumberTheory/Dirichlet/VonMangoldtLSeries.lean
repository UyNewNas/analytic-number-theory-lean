import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import AnalyticNumberTheory.Dirichlet.GRH

open scoped LSeries.notation ArithmeticFunction

namespace AnalyticNumberTheory
namespace Dirichlet

/-- On the half-plane `Re(s) > 1`, the Dirichlet-character twist of the von Mangoldt
L-series is the negative logarithmic derivative of mathlib's analytically continued
Dirichlet `LFunction`.

This is a neutral interface seam for explicit-formula arguments: it only identifies the
already-convergent twisted-von-Mangoldt series with the analytic `LFunction`. It does not
supply a contour shift, a GRH error term, or a prime-character-sum estimate. -/
theorem twistedVonMangoldtLSeries_eq_negLogDerivLFunction
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    L (↗χ * ↗Λ) s =
      -deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs

/-- Under GRH, the negative logarithmic derivative of a non-principal Dirichlet
`LFunction` is analytic at every point strictly to the right of the critical line.

This is the local regularity needed before contour-integral or explicit-formula arguments;
it does not supply any quantitative bound on the logarithmic derivative. -/
theorem GRHAt.analyticAt_negLogDerivLFunction
    {N : ℕ} [NeZero N] (hGRH : GRHAt N)
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : (1 / 2 : ℝ) < s.re) :
    AnalyticAt ℂ
      (fun z : ℂ ↦
        -deriv (DirichletCharacter.LFunction χ) z /
          DirichletCharacter.LFunction χ z) s := by
  have hL : AnalyticAt ℂ (DirichletCharacter.LFunction χ) s :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
  have hD : AnalyticAt ℂ (deriv (DirichletCharacter.LFunction χ)) s := hL.deriv
  exact hD.neg.div hL (hGRH.LFunction_ne_zero_of_half_lt_re χ hχ hs)

/-- Under GRH, the negative logarithmic derivative of every fixed non-principal
Dirichlet `LFunction` is analytic throughout the open half-plane `Re(s) > 1/2`. -/
theorem GRHAt.analyticOnNhd_negLogDerivLFunction_halfPlane
    {N : ℕ} [NeZero N] (hGRH : GRHAt N)
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    AnalyticOnNhd ℂ
      (fun z : ℂ ↦
        -deriv (DirichletCharacter.LFunction χ) z /
          DirichletCharacter.LFunction χ z)
      {s : ℂ | (1 / 2 : ℝ) < s.re} := by
  intro s hs
  exact hGRH.analyticAt_negLogDerivLFunction χ hχ hs

/-- Under GRH, the negative logarithmic derivative is uniformly bounded on every fixed
compact subset of the zero-free half-plane `Re(s) > 1/2`.

This is the compact-contour boundedness needed before a quantitative contour argument.  The
bound is qualitative: it does not give effective dependence on the modulus, the compact set,
or the contour height, and therefore does not by itself imply a GRH error term. -/
theorem GRHAt.exists_norm_negLogDerivLFunction_bound_on_compact
    {N : ℕ} [NeZero N] (hGRH : GRHAt N)
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {K : Set ℂ} (hK : IsCompact K)
    (hKhalf : K ⊆ {s : ℂ | (1 / 2 : ℝ) < s.re}) :
    ∃ C : ℝ, ∀ s ∈ K,
      ‖-deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s‖ ≤ C := by
  apply hK.exists_bound_of_continuousOn
  exact
    (hGRH.analyticOnNhd_negLogDerivLFunction_halfPlane χ hχ).continuousOn.mono hKhalf

/-- Under GRH, the negative logarithmic derivative of a fixed non-principal Dirichlet
`LFunction` is uniformly bounded on every finite vertical segment lying strictly to the
right of the critical line.

This packages the compact-contour theorem in the parameterization used by Perron and
explicit-formula contours. The bound is still qualitative in the height `T`; no vertical
growth estimate is asserted. -/
theorem GRHAt.exists_norm_negLogDerivLFunction_bound_on_verticalSegment
    {N : ℕ} [NeZero N] (hGRH : GRHAt N)
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {σ T : ℝ} (hσ : (1 / 2 : ℝ) < σ) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (-T) T,
      ‖-deriv (DirichletCharacter.LFunction χ)
            ((σ : ℂ) + (t : ℂ) * Complex.I) /
          DirichletCharacter.LFunction χ
            ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  let φ : ℝ → ℂ := fun t => (σ : ℂ) + (t : ℂ) * Complex.I
  let K : Set ℂ := φ '' Set.Icc (-T) T
  have hφ : Continuous φ := by
    fun_prop
  have hK : IsCompact K := isCompact_Icc.image hφ
  have hKhalf : K ⊆ {s : ℂ | (1 / 2 : ℝ) < s.re} := by
    intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    simpa [φ] using hσ
  obtain ⟨C, hC⟩ :=
    hGRH.exists_norm_negLogDerivLFunction_bound_on_compact χ hχ hK hKhalf
  refine ⟨C, ?_⟩
  intro t ht
  exact hC (φ t) ⟨t, ht, rfl⟩

/-- The absolute-convergence majorant for the von Mangoldt L-series on a real line
`Re(s) = σ`.  It depends only on `σ`, so it is uniform in the contour height and in the
Dirichlet-character modulus. -/
noncomputable def vonMangoldtLSeriesMajorant (σ : ℝ) : ℝ :=
  ∑' n : ℕ, ‖LSeries.term (↗Λ) (σ : ℂ) n‖

/-- On the absolutely convergent half-plane `Re(s) > 1`, the negative logarithmic
derivative of every Dirichlet `LFunction` is bounded by the untwisted von Mangoldt
majorant at the same real part.

Unlike the compactness bounds above, this is an effective right-half-plane majorant: the
right-hand side is an explicit convergent series depending only on `Re(s)` and is independent
of both the modulus and the imaginary part.  It is intended for the right edge of Perron or
explicit-formula contours; it does not control lines with `Re(s) ≤ 1`. -/
theorem norm_negLogDerivLFunction_le_vonMangoldtLSeriesMajorant
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    ‖-deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s‖ ≤ vonMangoldtLSeriesMajorant s.re := by
  rw [← twistedVonMangoldtLSeries_eq_negLogDerivLFunction χ hs]
  rw [vonMangoldtLSeriesMajorant, LSeries]
  have hχΛ := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  have hΛ : LSeriesSummable (↗Λ) (s.re : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hs)
  refine (norm_tsum_le_tsum_norm hχΛ.norm).trans ?_
  refine hχΛ.norm.tsum_le_tsum (fun n => ?_) hΛ.norm
  calc
    ‖LSeries.term (↗χ * ↗Λ) s n‖ ≤ ‖LSeries.term (↗Λ) s n‖ := by
      apply LSeries.norm_term_le
      simpa only [Pi.mul_apply, norm_mul] using
        mul_le_of_le_one_left (norm_nonneg (↗Λ n)) (χ.norm_le_one n)
    _ = ‖LSeries.term (↗Λ) (s.re : ℂ) n‖ := by
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
      simp

/-- Vertical-line form of `norm_negLogDerivLFunction_le_vonMangoldtLSeriesMajorant`.
For every fixed `σ > 1`, the same explicit majorant works uniformly for all heights `t`
and all Dirichlet moduli. -/
theorem norm_negLogDerivLFunction_le_vonMangoldtLSeriesMajorant_vertical
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {σ t : ℝ} (hσ : 1 < σ) :
    ‖-deriv (DirichletCharacter.LFunction χ)
          ((σ : ℂ) + (t : ℂ) * Complex.I) /
        DirichletCharacter.LFunction χ
          ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ vonMangoldtLSeriesMajorant σ := by
  have hs : 1 < (((σ : ℂ) + (t : ℂ) * Complex.I).re) := by
    simpa using hσ
  simpa using norm_negLogDerivLFunction_le_vonMangoldtLSeriesMajorant χ hs

/-- Explicit finite-height integral bound for the right vertical edge of a Perron-style
contour.  On `Re(s) = σ > 1`, integrating the negative logarithmic derivative from height
`-T` to `T` costs at most the contour length `2T` times the same height- and
modulus-independent von Mangoldt majorant.

This is deliberately only a right-edge estimate in the absolutely convergent half-plane;
it does not provide any control in `1/2 < Re(s) ≤ 1` or perform a Perron inversion. -/
theorem norm_intervalIntegral_negLogDerivLFunction_vertical_le
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {σ T : ℝ} (hσ : 1 < σ) (hT : 0 ≤ T) :
    ‖∫ t in (-T)..T,
        -deriv (DirichletCharacter.LFunction χ)
            ((σ : ℂ) + (t : ℂ) * Complex.I) /
          DirichletCharacter.LFunction χ
            ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      2 * T * vonMangoldtLSeriesMajorant σ := by
  calc
    ‖∫ t in (-T)..T,
        -deriv (DirichletCharacter.LFunction χ)
            ((σ : ℂ) + (t : ℂ) * Complex.I) /
          DirichletCharacter.LFunction χ
            ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        vonMangoldtLSeriesMajorant σ * |T - (-T)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      exact norm_negLogDerivLFunction_le_vonMangoldtLSeriesMajorant_vertical χ hσ
    _ = 2 * T * vonMangoldtLSeriesMajorant σ := by
      rw [abs_of_nonneg (by linarith : 0 ≤ T - (-T))]
      ring

/-- Perron's `1/s` kernel gains an explicit `1/σ` factor on the absolutely convergent
right edge.  This packages the first nontrivial kernel factor needed by a later truncated
Perron inversion while remaining strictly on `Re(s)=σ>1`.

No inversion or contour shift is asserted here; the hard effective control in
`1/2 < Re(s) ≤ 1` remains separate. -/
theorem norm_intervalIntegral_negLogDerivLFunction_div_vertical_le
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {σ T : ℝ} (hσ : 1 < σ) (hT : 0 ≤ T) :
    ‖∫ t in (-T)..T,
        (-deriv (DirichletCharacter.LFunction χ)
            ((σ : ℂ) + (t : ℂ) * Complex.I) /
          DirichletCharacter.LFunction χ
            ((σ : ℂ) + (t : ℂ) * Complex.I)) /
          ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (vonMangoldtLSeriesMajorant σ / σ) * (2 * T) := by
  have hσ0 : 0 < σ := lt_trans zero_lt_one hσ
  have hmajorant : 0 ≤ vonMangoldtLSeriesMajorant σ := by
    exact tsum_nonneg fun n => norm_nonneg _
  calc
    ‖∫ t in (-T)..T,
        (-deriv (DirichletCharacter.LFunction χ)
            ((σ : ℂ) + (t : ℂ) * Complex.I) /
          DirichletCharacter.LFunction χ
            ((σ : ℂ) + (t : ℂ) * Complex.I)) /
          ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        (vonMangoldtLSeriesMajorant σ / σ) * |T - (-T)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [norm_div]
      have hnum :=
        norm_negLogDerivLFunction_le_vonMangoldtLSeriesMajorant_vertical χ hσ
      have hden :
          σ ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
        simpa using Complex.re_le_norm ((σ : ℂ) + (t : ℂ) * Complex.I)
      exact
        (div_le_div_of_nonneg_right hnum (norm_nonneg _)).trans
          (div_le_div_of_nonneg_left hmajorant hσ0 hden)
    _ = (vonMangoldtLSeriesMajorant σ / σ) * (2 * T) := by
      rw [abs_of_nonneg (by linarith : 0 ≤ T - (-T))]
      ring

end Dirichlet
end AnalyticNumberTheory
