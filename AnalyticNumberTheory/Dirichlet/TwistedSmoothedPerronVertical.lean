import AnalyticNumberTheory.Dirichlet.TwistedSmoothedPerronHorizontal

/-!
# Character-neutral vertical contour bound for twisted smoothed Perron inversion

Provenance-preserving extraction of the vertical-edge argument inside
`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`, module
`MathlibNt/AnalyticNumberTheory/LargeSieve/DirichLTwistedSmoothedContourNormBounds.lean`.

The source packages the vertical estimate with a nonquadratic conductor-logarithmic contour.  This
module exposes only the neutral analytic calculation: the caller supplies a uniform logarithmic-
derivative bound `J` on one finite vertical segment.  No GRH, zero-free region, character-type
hypothesis, conductor-log parameter, or downstream application appears in the theorem.
-/

open Set Function Filter Complex Real MeasureTheory

namespace AnalyticNumberTheory.Dirichlet

/-- A finite vertical Mellin--Bochner estimate independent of how the logarithmic-derivative bound
is obtained.  The factor `8` is `4` from the Mellin decay on `Re(s) >= 1/2` times the interval
length `2T`. -/
theorem norm_twistedSmoothedPerron_vertical_le_of_logDeriv_bound
    {ν : ℝ → ℝ} {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε)
    (hMellin : ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) s‖ ≤ M * (ε * ‖s‖ ^ 2)⁻¹)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a T X J : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (ha2 : a ≤ 2)
    (hT : 0 ≤ T) (hX : 1 ≤ X) (hJ : 0 ≤ J)
    (hlog : ∀ t : ℝ, |t| ≤ T →
      ‖deriv χ.LFunction (a + t * I) / χ.LFunction (a + t * I)‖ ≤ J) :
    ‖VIntegral (twistedSmoothedPerronIntegrand χ ν ε X) a (-T) T‖ ≤
      8 * M * J * T * X ^ a / ε := by
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hpoint (t : ℝ) (ht : |t| ≤ T) :
      ‖twistedSmoothedPerronIntegrand χ ν ε X (a + t * I)‖ ≤
        J * (4 * M / ε) * X ^ a := by
    have hm := hMellin (a + t * I) (by simp; exact ha) (by simp; exact ha2)
    have hnormsq : (1 / 4 : ℝ) ≤ ‖(a : ℂ) + t * I‖ ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
      nlinarith [sq_nonneg t]
    have hinv : (ε * ‖(a : ℂ) + t * I‖ ^ 2)⁻¹ ≤ 4 / ε := by
      rw [mul_inv_rev]
      have hi : (‖(a : ℂ) + t * I‖ ^ 2)⁻¹ ≤ (4 : ℝ) := by
        have h := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 4) hnormsq
        norm_num at h ⊢
        exact h
      calc
        (‖(a : ℂ) + t * I‖ ^ 2)⁻¹ * ε⁻¹ ≤ 4 * ε⁻¹ :=
          mul_le_mul_of_nonneg_right hi (inv_nonneg.mpr hε.le)
        _ = 4 / ε := by rw [div_eq_mul_inv]
    have hm' : ‖mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (a + t * I)‖ ≤
        4 * M / ε := by
      calc
        _ ≤ M * (ε * ‖(a : ℂ) + t * I‖ ^ 2)⁻¹ := hm
        _ ≤ M * (4 / ε) := mul_le_mul_of_nonneg_left hinv hM
        _ = 4 * M / ε := by ring
    have hXnorm : ‖(X : ℂ) ^ ((a : ℂ) + t * I)‖ = X ^ a := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX0]
      simp
    have hlog' :
        ‖-deriv χ.LFunction (a + t * I) / χ.LFunction (a + t * I)‖ ≤ J := by
      simpa only [neg_div, norm_neg] using hlog t ht
    dsimp only [twistedSmoothedPerronIntegrand]
    rw [norm_mul, norm_mul, hXnorm]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hlog' hm' (norm_nonneg _) hJ) (Real.rpow_nonneg hX0.le _)
  rw [VIntegral, norm_smul, norm_I, one_mul]
  calc
    ‖∫ t in -T..T, twistedSmoothedPerronIntegrand χ ν ε X (a + t * I)‖ ≤
        (J * (4 * M / ε) * X ^ a) * |T - (-T)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [uIoc_of_le (by linarith)] at ht
      apply hpoint t
      rw [abs_le]
      exact ⟨ht.1.le, ht.2⟩
    _ = 8 * M * J * T * X ^ a / ε := by
      rw [abs_of_nonneg (by linarith : 0 ≤ T - (-T))]
      ring

end AnalyticNumberTheory.Dirichlet
