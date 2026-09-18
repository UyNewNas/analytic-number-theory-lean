import AnalyticNumberTheory.Dirichlet.TwistedSmoothedPsiClose

/-!
# Uniform character-neutral unsmoothing

This module records the stronger quantifier order already formalized in
`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`, module
`MathlibNt/AnalyticNumberTheory/LargeSieve/DirichLTwistedNonquadraticPointwiseSiegelWalfisz.lean`,
theorem `exists_uniform_twistedSmoothedPsiClose`.

Despite its source-file location, the theorem itself is character-neutral: the smoothing
constant is chosen before the modulus and character.  We reuse ANT's neutral transition-band
core and cumulative von-Mangoldt prefix, without importing the Goldbach pointwise
Siegel--Walfisz hierarchy.
-/

open Set Function Filter Complex Real MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace AnalyticNumberTheory.Dirichlet

/-- The smoothing-removal constant is uniform in the modulus and character.  This is the
quantifier order needed by downstream pointwise GRH applications. -/
theorem exists_uniform_twistedSmoothedPsiClose
    {SmoothingF : ℝ → ℝ} (_diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      (X : ℝ), 3 < X → ∀ (ε : ℝ), 0 < ε → ε < 1 → 2 < X * ε →
      ‖twistedSmoothedPsi χ SmoothingF ε X -
        vonMangoldtCharacterPartialSum q ⌊X⌋₊ χ‖ ≤ C * ε * X * Real.log X := by
  obtain ⟨c₁, c₁_pos, c₁_eq, hc₁⟩ :=
    Smooth1Properties_below suppSmoothingF mass_one
  obtain ⟨c₂, c₂_pos, c₂_eq, hc₂⟩ :=
    Smooth1Properties_above suppSmoothingF
  have c₁_lt : c₁ < 1 := by
    rw [c₁_eq]
    exact lt_trans Real.log_two_lt_d9 (by norm_num)
  have c₂_lt : c₂ < 2 := by
    rw [c₂_eq]
    nth_rewrite 3 [← mul_one 2]
    apply mul_lt_mul'
    · rfl
    · exact lt_trans Real.log_two_lt_d9 (by norm_num)
    · exact Real.log_nonneg (by norm_num)
    · positivity
  let C₀ : ℝ := 6 * (3 * c₁ + c₂)
  have C₀_pos : 0 < C₀ := by
    dsimp [C₀]
    positivity
  refine ⟨2 * C₀, mul_pos (by norm_num) C₀_pos, ?_⟩
  intro q _ χ X X_gt_three ε ε_pos ε_lt_one Xε_gt_two
  have X_pos : 0 < X := by linarith
  have n_div_X_pos {n : ℕ} (hn : 0 < n) : 0 < (n : ℝ) / X := by
    positivity
  have smoothAbove (n : ℕ) (hn : 0 < n) :
      Smooth1 SmoothingF ε (n / X) ≤ 1 :=
    Smooth1LeOne SmoothingFnonneg mass_one ε_pos (n_div_X_pos hn)
  have smoothBelow (n : ℕ) (hn : 0 < n) :
      0 ≤ Smooth1 SmoothingF ε (n / X) :=
    Smooth1Nonneg SmoothingFnonneg (n_div_X_pos hn) ε_pos
  have smoothOne (n : ℕ) (hn : 0 < n)
      (hnle : (n : ℝ) ≤ X * (1 - c₁ * ε)) :
      Smooth1 SmoothingF ε (n / X) = 1 := by
    apply hc₁ (ε := ε) (n / X) ε_pos (n_div_X_pos hn)
    exact (div_le_iff₀' X_pos).mpr hnle
  have smoothZero (n : ℕ)
      (hn : 1 + c₂ * ε ≤ (n : ℝ) / X) :
      Smooth1 SmoothingF ε (n / X) = 0 :=
    hc₂ (ε := ε) (n / X) ⟨ε_pos, ε_lt_one⟩ hn
  have X_bound_1 : 1 ≤ X * ε * c₁ := by
    rw [c₁_eq, ← div_le_iff₀]
    · have h : 1 / Real.log 2 < 2 := by
        nth_rewrite 2 [← one_div_one_div 2]
        rw [one_div_lt_one_div]
        · exact lt_of_le_of_lt (by norm_num) Real.log_two_gt_d9
        · exact Real.log_pos (by norm_num)
        · norm_num
      exact le_of_lt (h.trans Xε_gt_two)
    · exact Real.log_pos (by norm_num)
  have X_bound_2 : 1 ≤ X * ε * c₂ := by
    rw [c₂_eq, ← div_le_iff₀]
    · have h : 1 / (2 * Real.log 2) < 2 := by
        nth_rewrite 3 [← one_div_one_div 2]
        rw [one_div_lt_one_div, ← one_mul (1 / 2)]
        · apply mul_lt_mul
          · norm_num
          · exact le_of_lt (lt_trans (by norm_num) Real.log_two_gt_d9)
          · norm_num
          · norm_num
        · norm_num
          exact Real.log_pos (by norm_num)
        · norm_num
      exact le_of_lt (h.trans Xε_gt_two)
    · norm_num
      exact Real.log_pos (by norm_num)
  exact twistedSmoothedPsiClose_aux
    SmoothingF c₁ c₁_pos c₁_lt c₂ c₂_pos c₂_lt hc₂ C₀ rfl
    ε ε_pos ε_lt_one X X_pos X_gt_three X_bound_1 X_bound_2
    smoothAbove smoothBelow smoothOne smoothZero χ

end AnalyticNumberTheory.Dirichlet
