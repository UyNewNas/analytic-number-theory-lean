import AnalyticNumberTheory.ComplexAnalysis.LocalZeroQuotient
import AnalyticNumberTheory.ComplexAnalysis.JensenDivisorBound
import AnalyticNumberTheory.Dirichlet.LocalLogDerivative
import AnalyticNumberTheory.Dirichlet.LocalLogDerivativeFixedRadii
import Mathlib.Tactic

/-!
# Quantitative local-zero quotient bound

Consumer-driven neutral continuation of the finite regularized-zero quotient layer.

The radii and proof architecture follow the Landau/Borel--Caratheodory argument in
`anthropics/formal-math@fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`,
`zeta23/Zeta23/WeilEF/Landau.lean::norm_logDeriv_Cf_le`, while reusing ANT's
already-integrated normalized Jensen multiplicity bound, regularized quotient, holomorphic-log
existence theorem, and fixed-radius derivative bridge.

No Dirichlet character, GRH premise, contour argument, or downstream application parameter occurs
in the statement.
-/

open Complex Set Metric Filter
open Classical
open scoped Topology

namespace AnalyticNumberTheory.ComplexAnalysis

noncomputable section

/-- If `f` is normalized by `f 0 = 1`, analytic on the unit disc, and bounded by `B` on
`‖z‖ ≤ 24/25`, then after dividing out all zeros through radius `22/25`, the regular part has
logarithmic derivative at most `520800 * log B` on `‖z‖ ≤ 83/100`.

The numerical improvement over the source's `44795000` coefficient comes only from ANT's verified
tight-radius `17/20 -> 21/25 -> 83/100` Borel--Caratheodory/Cauchy derivative bridge; the zero-count
and quotient-growth bookkeeping are otherwise the same source-shaped argument. -/
theorem norm_logDeriv_regularizedFiniteZeroQuotient_le
    {f : ℂ → ℂ} {B : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1))
    (hf0 : f 0 = 1)
    (hfin : (SetOfZeros 1 f).Finite)
    (hB2 : 2 ≤ B)
    (hfB : ∀ w : ℂ, ‖w‖ ≤ (24 : ℝ) / 25 → ‖f w‖ ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ (83 : ℝ) / 100) :
    ‖logDeriv (regularizedFiniteZeroQuotient ((22 : ℝ) / 25) f) z‖ ≤
      520800 * Real.log B := by
  have hf0' : f 0 ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hfinr : (SetOfZeros ((22 : ℝ) / 25) f).Finite :=
    finiteSetOfZeros_mono (by norm_num : (22 : ℝ) / 25 ≤ 1) hfin
  set K : ℕ := ∑ ρ ∈ hfinr.toFinset, analyticOrderNatAt f ρ with hK
  have hB1 : 1 ≤ B := by linarith
  have hAnalytic24 : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) ((24 : ℝ) / 25)) := by
    intro w hw
    apply hf w
    rw [mem_closedBall, dist_zero_right] at hw ⊢
    linarith
  have hcountRaw :=
    jensenZeroMultiplicityBound_normalized
      (f := f) (B := B) (r := (22 : ℝ) / 25) (R := (24 : ℝ) / 25)
      (by norm_num) (by norm_num) hB1 hAnalytic24 hf0
      (fun w hw => hfB w (by
        rw [mem_sphere, dist_zero_right] at hw
        exact hw.le))
  have hcount :
      (K : ℝ) ≤ Real.log B / Real.log (((24 : ℝ) / 25) / ((22 : ℝ) / 25)) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfinr] at hcountRaw
    simpa [K] using hcountRaw
  have hsphere : ∀ w : ℂ, ‖w‖ = (24 : ℝ) / 25 →
      ‖regularizedFiniteZeroQuotient ((22 : ℝ) / 25) f w‖ ≤
        B * ((25 : ℝ) / 2) ^ K := by
    intro w hw
    have hwmem : w ∉ SetOfZeros ((22 : ℝ) / 25) f := by
      intro h
      have := h.1
      rw [hw] at this
      norm_num at this
    have hdist : ∀ ρ ∈ hfinr.toFinset, ((2 : ℝ) / 25) ≤ ‖w - ρ‖ := by
      intro ρ hρ
      have hρ' := hfinr.mem_toFinset.mp hρ
      calc
        ((2 : ℝ) / 25) = (24 : ℝ) / 25 - (22 : ℝ) / 25 := by norm_num
        _ ≤ ‖w‖ - ‖ρ‖ := by
          rw [hw]
          linarith [hρ'.1]
        _ ≤ ‖w - ρ‖ := norm_sub_norm_le w ρ
    have hprod_lb :
        ((2 : ℝ) / 25) ^ K ≤
          ‖∏ ρ ∈ hfinr.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ‖ := by
      rw [norm_prod, hK, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod (fun ρ _ => by positivity) (fun ρ hρ => ?_)
      rw [norm_pow]
      exact pow_le_pow_left₀ (by norm_num) (hdist ρ hρ) _
    unfold regularizedFiniteZeroQuotient
    rw [dif_pos hfinr, dif_neg hwmem, norm_div]
    have hprod_pos :
        (0 : ℝ) < ‖∏ ρ ∈ hfinr.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ‖ :=
      lt_of_lt_of_le (by positivity) hprod_lb
    rw [div_le_iff₀ hprod_pos]
    calc
      ‖f w‖ ≤ B := hfB w (le_of_eq hw)
      _ = B * ((25 : ℝ) / 2) ^ K * ((2 : ℝ) / 25) ^ K := by
        rw [mul_assoc, ← mul_pow]
        norm_num
      _ ≤ B * ((25 : ℝ) / 2) ^ K *
          ‖∏ ρ ∈ hfinr.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ‖ := by
        have hnonneg : (0 : ℝ) ≤ B * ((25 : ℝ) / 2) ^ K := by positivity
        exact mul_le_mul_of_nonneg_left hprod_lb hnonneg
  have hQAnalytic24 : AnalyticOn ℂ
      (regularizedFiniteZeroQuotient ((22 : ℝ) / 25) f)
      (closedBall (0 : ℂ) ((24 : ℝ) / 25)) :=
    (analyticOnNhd_regularizedFiniteZeroQuotient
      (by norm_num : (22 : ℝ) / 25 < (24 : ℝ) / 25)
      (by norm_num : (24 : ℝ) / 25 < 1) hf hf0').analyticOn
  have hball : ∀ w : ℂ, ‖w‖ ≤ (24 : ℝ) / 25 →
      ‖regularizedFiniteZeroQuotient ((22 : ℝ) / 25) f w‖ ≤
        B * ((25 : ℝ) / 2) ^ K := by
    intro w hw
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
      (U := closedBall (0 : ℂ) ((24 : ℝ) / 25)) Metric.isBounded_closedBall
    · apply DifferentiableOn.diffContOnCl
      rw [Metric.closure_closedBall]
      exact hQAnalytic24.differentiableOn
    · rw [frontier_closedBall']
      intro v hv
      refine hsphere v ?_
      simpa [mem_sphere, dist_zero_right] using hv
    · rw [Metric.closure_closedBall]
      simpa [mem_closedBall, dist_zero_right] using hw
  have hQ0 : (1 : ℝ) ≤
      ‖regularizedFiniteZeroQuotient ((22 : ℝ) / 25) f 0‖ := by
    have h0mem : (0 : ℂ) ∉ SetOfZeros ((22 : ℝ) / 25) f := fun h => hf0' h.2
    unfold regularizedFiniteZeroQuotient
    rw [dif_pos hfinr, dif_neg h0mem, norm_div, hf0, norm_one]
    rw [le_div_iff₀]
    · rw [one_mul, norm_prod]
      refine Finset.prod_le_one (fun ρ _ => by positivity) (fun ρ hρ => ?_)
      have hρ' := hfinr.mem_toFinset.mp hρ
      rw [norm_pow, zero_sub, norm_neg]
      exact pow_le_one₀ (norm_nonneg _) (by linarith [hρ'.1])
    · rw [norm_prod]
      refine Finset.prod_pos (fun ρ hρ => ?_)
      have hρ' := hfinr.mem_toFinset.mp hρ
      have hρ0 : ρ ≠ 0 := by
        rintro rfl
        exact hf0' hρ'.2
      rw [norm_pow, zero_sub, norm_neg]
      exact pow_pos (norm_pos_iff.mpr hρ0) _
  let Q : ℂ → ℂ := regularizedFiniteZeroQuotient ((22 : ℝ) / 25) f
  have hQd : DifferentiableOn ℂ Q (ball (0 : ℂ) ((17 : ℝ) / 20)) := by
    intro w hw
    have hw90 : w ∈ closedBall (0 : ℂ) ((9 : ℝ) / 10) := by
      rw [mem_ball, dist_zero_right] at hw
      rw [mem_closedBall, dist_zero_right]
      linarith
    exact ((analyticOnNhd_regularizedFiniteZeroQuotient
      (by norm_num : (22 : ℝ) / 25 < (9 : ℝ) / 10)
      (by norm_num : (9 : ℝ) / 10 < 1) hf hf0') w hw90).differentiableAt.differentiableWithinAt
  have hQne : ∀ w ∈ ball (0 : ℂ) ((17 : ℝ) / 20), Q w ≠ 0 := by
    intro w hw
    apply regularizedFiniteZeroQuotient_ne_zero hf hf0'
      (by norm_num : (22 : ℝ) / 25 < 1) hfin
    rw [mem_ball, dist_zero_right] at hw
    exact hw.le.trans (by norm_num : (17 : ℝ) / 20 ≤ (22 : ℝ) / 25)
  obtain ⟨J, hJd, hexp⟩ :=
    AnalyticNumberTheory.Dirichlet.exists_holomorphicLog_on_ball
      Q 0 (by norm_num : (0 : ℝ) < (17 : ℝ) / 20) hQd hQne
  have hre : ∀ w ∈ ball (0 : ℂ) ((17 : ℝ) / 20),
      (J w).re = Real.log ‖Q w‖ := by
    intro w hw
    rw [← hexp hw, norm_exp, Real.log_exp]
  set A : ℝ :=
    (1 + Real.log ((25 : ℝ) / 2) /
      Real.log (((24 : ℝ) / 25) / ((22 : ℝ) / 25))) * Real.log B with hA
  have hlogratio :
      (0 : ℝ) < Real.log (((24 : ℝ) / 25) / ((22 : ℝ) / 25)) :=
    Real.log_pos (by norm_num)
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hApos : 0 < A := by
    rw [hA]
    have hcoef :
        (0 : ℝ) < 1 + Real.log ((25 : ℝ) / 2) /
          Real.log (((24 : ℝ) / 25) / ((22 : ℝ) / 25)) := by positivity
    positivity
  have hosc : ∀ w ∈ ball (0 : ℂ) ((17 : ℝ) / 20), (J w).re - (J 0).re ≤ A := by
    intro w hw
    rw [hre w hw, hre 0 (mem_ball_self (by norm_num : (0 : ℝ) < (17 : ℝ) / 20))]
    have hw24 : ‖w‖ ≤ (24 : ℝ) / 25 := by
      rw [mem_ball, dist_zero_right] at hw
      linarith
    have hQw : ‖Q w‖ ≤ B * ((25 : ℝ) / 2) ^ K := by
      simpa [Q] using hball w hw24
    have hQwpos : 0 < ‖Q w‖ := norm_pos_iff.mpr (hQne w hw)
    have h1 : Real.log ‖Q w‖ ≤ Real.log (B * ((25 : ℝ) / 2) ^ K) :=
      Real.log_le_log hQwpos hQw
    have h2 : 0 ≤ Real.log ‖Q 0‖ := by
      apply Real.log_nonneg
      simpa [Q] using hQ0
    have h3 : Real.log (B * ((25 : ℝ) / 2) ^ K) =
        Real.log B + K * Real.log ((25 : ℝ) / 2) := by
      rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
    have h4 : (K : ℝ) * Real.log ((25 : ℝ) / 2) ≤
        (Real.log B / Real.log (((24 : ℝ) / 25) / ((22 : ℝ) / 25))) *
          Real.log ((25 : ℝ) / 2) := by
      exact mul_le_mul_of_nonneg_right hcount (Real.log_nonneg (by norm_num))
    rw [hA]
    calc
      Real.log ‖Q w‖ - Real.log ‖Q 0‖
          ≤ Real.log B + (K : ℝ) * Real.log ((25 : ℝ) / 2) := by
            rw [← h3]
            linarith
      _ ≤ Real.log B +
          (Real.log B / Real.log (((24 : ℝ) / 25) / ((22 : ℝ) / 25))) *
            Real.log ((25 : ℝ) / 2) := by linarith
      _ = (1 + Real.log ((25 : ℝ) / 2) /
          Real.log (((24 : ℝ) / 25) / ((22 : ℝ) / 25))) * Real.log B := by
            field_simp
  have hdz := AnalyticNumberTheory.Dirichlet.norm_deriv_le_fixed_radii_83_100
    J 0 z hApos hJd hosc (by simpa [dist_zero_right] using hz)
  have hzmem : z ∈ ball (0 : ℂ) ((17 : ℝ) / 20) := by
    rw [mem_ball, dist_zero_right]
    linarith
  have hJat := (hJd z hzmem).differentiableAt (isOpen_ball.mem_nhds hzmem)
  have hevent : (fun w => exp (J w)) =ᶠ[𝓝 z] Q := by
    filter_upwards [isOpen_ball.mem_nhds hzmem] with w hw
    exact hexp hw
  have hderivQ : deriv Q z = Q z * deriv J z := by
    rw [← hevent.deriv_eq]
    simpa [hexp hzmem] using hJat.hasDerivAt.cexp.deriv
  have hlogDeriv : logDeriv Q z = deriv J z := by
    rw [logDeriv_apply, hderivQ, mul_div_cancel_left₀ _ (hQne z hzmem)]
  rw [show regularizedFiniteZeroQuotient ((22 : ℝ) / 25) f = Q by rfl, hlogDeriv]
  refine hdz.trans ?_
  have hcoef : A ≤ 31 * Real.log B := by
    rw [hA]
    have hlog25 :
        Real.log ((25 : ℝ) / 2) ≤
          30 * Real.log (((24 : ℝ) / 25) / ((22 : ℝ) / 25)) := by
      have hp :
          ((25 : ℝ) / 2) ≤ (((24 : ℝ) / 25) / ((22 : ℝ) / 25)) ^ (30 : ℕ) := by
        norm_num
      calc
        Real.log ((25 : ℝ) / 2) ≤
            Real.log ((((24 : ℝ) / 25) / ((22 : ℝ) / 25)) ^ (30 : ℕ)) :=
          Real.log_le_log (by norm_num) hp
        _ = 30 * Real.log (((24 : ℝ) / 25) / ((22 : ℝ) / 25)) := by
          rw [Real.log_pow]
          norm_num
    have hfrac :
        Real.log ((25 : ℝ) / 2) /
            Real.log (((24 : ℝ) / 25) / ((22 : ℝ) / 25)) ≤ 30 :=
      (div_le_iff₀ hlogratio).2 (by linarith)
    have hpre :
        1 + Real.log ((25 : ℝ) / 2) /
            Real.log (((24 : ℝ) / 25) / ((22 : ℝ) / 25)) ≤ 31 := by linarith
    exact mul_le_mul_of_nonneg_right hpre hlogB.le
  calc
    16800 * A ≤ 16800 * (31 * Real.log B) :=
      mul_le_mul_of_nonneg_left hcoef (by norm_num)
    _ = 520800 * Real.log B := by ring

end

end AnalyticNumberTheory.ComplexAnalysis
