import AnalyticNumberTheory.Dirichlet.TwistedSmoothedPerronRight

/-!
# Horizontal contour bound for twisted smoothed Perron inversion

Provenance-preserving extraction from
`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`, module
`MathlibNt/AnalyticNumberTheory/LargeSieve/DirichLTwistedSmoothedContourNormBounds.lean`.

Only the character-neutral horizontal estimate is ported: the caller supplies a uniform
logarithmic-derivative bound `J` on the horizontal segment.  No GRH, nonquadratic-character
hypothesis, conductor-log specialization, Goldbach object, or downstream parameter choice appears
in this module.
-/

open Set Function Filter Complex Real MeasureTheory

namespace AnalyticNumberTheory.Dirichlet

/-- A horizontal Mellin--Bochner estimate independent of how the logarithmic-derivative bound is
obtained.  This is the reusable seam needed by consumers that supply their own zero-free/GRH input. -/
theorem norm_twistedSmoothedPerron_horizontal_le_of_logDeriv_bound
    {ν : ℝ → ℝ} {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε)
    (hMellin : ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ M * (ε * ‖s‖ ^ 2)⁻¹)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a b T t X J : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (hab : a ≤ b)
    (hb : b ≤ 2) (hT : 1 ≤ T) (ht : |t| = T) (hX : 1 ≤ X) (hJ : 0 ≤ J)
    (hlog : ∀ σ : ℝ, a ≤ σ → σ ≤ b →
      ‖deriv χ.LFunction (σ + t * I) / χ.LFunction (σ + t * I)‖ ≤ J) :
    ‖HIntegral (twistedSmoothedPerronIntegrand χ ν ε X) a b t‖ ≤
      4 * M * J * X ^ b / (ε * (1 + T ^ 2)) := by
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hT0 : 0 < T := by linarith
  have hpoint (σ : ℝ) (hσa : a ≤ σ) (hσb : σ ≤ b) :
      ‖twistedSmoothedPerronIntegrand χ ν ε X (σ + t * I)‖ ≤
        J * (2 * M / (ε * (1 + T ^ 2))) * X ^ b := by
    have hm := hMellin (σ + t * I) (by simp; linarith) (by simp; exact hσb.trans hb)
    have hnormsq : T ^ 2 ≤ ‖(σ : ℂ) + t * I‖ ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
      have ht2 := congrArg (fun u : ℝ => u ^ 2) ht
      rw [sq_abs] at ht2
      nlinarith [sq_nonneg σ]
    have hinvDen : (T ^ 2)⁻¹ ≤ 2 * (1 + T ^ 2)⁻¹ := by
      rw [show (T ^ 2)⁻¹ = 1 / T ^ 2 by rw [one_div],
        show 2 * (1 + T ^ 2)⁻¹ = 2 / (1 + T ^ 2) by rw [div_eq_mul_inv]]
      rw [div_le_div_iff₀ (sq_pos_of_pos hT0) (by positivity)]
      nlinarith [sq_nonneg T]
    have hm' : ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ + t * I)‖ ≤
        2 * M / (ε * (1 + T ^ 2)) := by
      calc
        _ ≤ M * (ε * ‖(σ : ℂ) + t * I‖ ^ 2)⁻¹ := hm
        _ ≤ M * (2 / (ε * (1 + T ^ 2))) := by
          gcongr
          rw [mul_inv_rev]
          calc
            (‖(σ : ℂ) + t * I‖ ^ 2)⁻¹ * ε⁻¹ ≤
                (2 * (1 + T ^ 2)⁻¹) * ε⁻¹ := by
              gcongr
              exact (inv_anti₀ (sq_pos_of_pos hT0) hnormsq).trans hinvDen
            _ = 2 / (ε * (1 + T ^ 2)) := by field_simp [hε.ne']
        _ = 2 * M / (ε * (1 + T ^ 2)) := by ring
    have hXnorm : ‖(X : ℂ) ^ ((σ : ℂ) + t * I)‖ = X ^ σ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX0]
      simp
    have hXpow : X ^ σ ≤ X ^ b := Real.rpow_le_rpow_of_exponent_le hX hσb
    have hlog' : ‖-deriv χ.LFunction (σ + t * I) / χ.LFunction (σ + t * I)‖ ≤ J := by
      simpa only [neg_div, norm_neg] using hlog σ hσa hσb
    dsimp only [twistedSmoothedPerronIntegrand]
    rw [norm_mul, norm_mul, hXnorm]
    calc
      _ ≤ J * (2 * M / (ε * (1 + T ^ 2))) * X ^ σ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hlog' hm' (norm_nonneg _) hJ) (Real.rpow_nonneg hX0.le _)
      _ ≤ _ := by gcongr
  rw [HIntegral]
  calc
    _ ≤ (J * (2 * M / (ε * (1 + T ^ 2))) * X ^ b) * |b - a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro σ hσ
      rw [uIoc_of_le hab] at hσ
      exact hpoint σ hσ.1.le hσ.2
    _ ≤ (J * (2 * M / (ε * (1 + T ^ 2))) * X ^ b) * 2 := by
      have hlen : |b - a| ≤ 2 := by
        rw [abs_of_nonneg (sub_nonneg.mpr hab)]
        linarith
      gcongr
    _ = _ := by ring

end AnalyticNumberTheory.Dirichlet
