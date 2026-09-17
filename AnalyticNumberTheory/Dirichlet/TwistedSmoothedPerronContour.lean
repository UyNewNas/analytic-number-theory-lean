import AnalyticNumberTheory.Dirichlet.TwistedSmoothedPerronHorizontal

/-!
# Finite contour identity and error assembly for twisted smoothed Perron inversion

Provenance-preserving extraction of the character-neutral rectangle step used in
`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`, modules
`MathlibNt/AnalyticNumberTheory/LargeSieve/DirichLTwistedSmoothedConductorLogEdges.lean` and
`MathlibNt/AnalyticNumberTheory/LargeSieve/DirichLTwistedSmoothedNonquadraticErrorAssembly.lean`.

The external application packages its contour with a nonquadratic-character hypothesis.  The
actual rectangle identity and subsequent norm assembly do not need that arithmetic specialization:
once holomorphy, the finite edge identity, edge bounds, and right-line integrability are supplied by
the caller, the rest is pure contour algebra.  Downstream consumers can therefore obtain those
inputs from their own zero-free/GRH argument without duplicating rectangle-integration machinery.
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

/-- Split an integrable real-line integral into lower tail, finite middle interval, and upper tail.
This is the measure-theoretic normalization used after a finite contour shift. -/
theorem integral_lower_middle_upper
    (f : ℝ → ℂ) {T : ℝ} (hf : Integrable f) (hT : 0 ≤ T) :
    (∫ t in Iic (-T), f t) + (∫ t in Ioc (-T) T, f t) +
        (∫ t in Ici T, f t) = ∫ t, f t := by
  have h₁ := integral_add_compl (μ := volume) (s := Iic (-T)) measurableSet_Iic hf
  have h₂ := integral_add_compl (μ := volume.restrict (Ioi (-T)))
    (s := Iic T) measurableSet_Iic hf.integrableOn
  rw [integral_Ici_eq_integral_Ioi]
  simp only [compl_Iic] at h₁ h₂
  have hi : Iic T ∩ Ioi (-T) = Ioc (-T) T := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_Ioc]
    tauto
  have hc : Ioi T ∩ Ioi (-T) = Ioi T := by
    ext x
    simp only [mem_inter_iff, mem_Ioi]
    constructor
    · exact fun hx => hx.1
    · intro hx
      exact ⟨hx, by linarith⟩
  rw [Measure.restrict_restrict measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Ioi] at h₂
  rw [hi, hc] at h₂
  linear_combination h₁ + h₂

/-- Normalize a finite contour shift after bounding its three non-right edges and both tails of the
integrable right line.  No zero-free, GRH, or arithmetic hypothesis is needed once the exact finite
shift identity and the five norm bounds are supplied.

This is the neutral error-assembly seam used before an application chooses its left edge and
quantitative contour parameters. -/
theorem norm_verticalIntegral'_le_of_finite_contour_bounds
    (F : ℂ → ℂ) {a b T Vl Hu Hl Tl Tu : ℝ} (hT : 0 ≤ T)
    (hf : Integrable (fun t : ℝ => F ((b : ℂ) + t * I)))
    (hshift : VIntegral F b (-T) T - VIntegral F a (-T) T =
      HIntegral F a b T - HIntegral F a b (-T))
    (hleft : ‖VIntegral F a (-T) T‖ ≤ Vl)
    (htop : ‖HIntegral F a b T‖ ≤ Hu)
    (hbottom : ‖HIntegral F a b (-T)‖ ≤ Hl)
    (htlow : ‖∫ t in Iic (-T), F ((b : ℂ) + t * I)‖ ≤ Tl)
    (htupper : ‖∫ t in Ici T, F ((b : ℂ) + t * I)‖ ≤ Tu) :
    ‖VerticalIntegral' F b‖ ≤ Tl + (Vl + Hu + Hl) + Tu := by
  have hsplit := integral_lower_middle_upper
    (fun t : ℝ => F ((b : ℂ) + t * I)) hf hT
  have hmid :
      ‖∫ t in Ioc (-T) T, F ((b : ℂ) + t * I)‖ =
        ‖VIntegral F b (-T) T‖ := by
    rw [VIntegral, norm_smul, norm_I, one_mul,
      intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  have hv : ‖VIntegral F b (-T) T‖ ≤ Vl + Hu + Hl := by
    have heq : VIntegral F b (-T) T =
        VIntegral F a (-T) T + HIntegral F a b T - HIntegral F a b (-T) := by
      linear_combination hshift
    rw [heq]
    exact ((norm_sub_le _ _).trans
      (add_le_add (norm_add_le _ _) (le_refl _))).trans
        (add_le_add (add_le_add hleft htop) hbottom)
  have hfull : ‖∫ t : ℝ, F ((b : ℂ) + t * I)‖ ≤ Tl + (Vl + Hu + Hl) + Tu := by
    rw [← hsplit]
    calc
      _ ≤ ‖∫ t in Iic (-T), F ((b : ℂ) + t * I)‖ +
          ‖∫ t in Ioc (-T) T, F ((b : ℂ) + t * I)‖ +
          ‖∫ t in Ici T, F ((b : ℂ) + t * I)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
      _ ≤ _ := by
        rw [hmid]
        exact add_le_add (add_le_add htlow hv) htupper
  have hnorm : ‖(1 / (2 * (Real.pi : ℂ) * I) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, norm_I]
    norm_num
    rw [abs_of_pos Real.pi_pos]
    have hinv : Real.pi⁻¹ ≤ 1 :=
      (inv_le_one₀ Real.pi_pos).2 (by linarith [Real.pi_gt_three])
    nlinarith [inv_nonneg.mpr Real.pi_pos.le]
  have hnormalized : ‖VerticalIntegral' F b‖ ≤
      ‖∫ t : ℝ, F ((b : ℂ) + t * I)‖ := by
    rw [VerticalIntegral', VerticalIntegral, norm_smul, norm_smul, norm_I, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hnorm
  exact hnormalized.trans hfull

end AnalyticNumberTheory.Dirichlet