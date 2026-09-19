/-
Copyright (c) 2026 UyNewNas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Source/API audit:
* `anthropics/formal-math@fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`,
  `zeta23/Zeta23/FromPNTPlus/StrongPNTPrefix.lean`, declarations
  `ZeroFactor`, `ZeroFactorization`, `Cf`, `CfAnalytic`, and
  `zeta23/Zeta23/WeilEF/Landau.lean`, declarations `Cf_ne_zero`,
  `f_eq_prod_mul_Cf`, `logDeriv_split`.
* Pinned Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` supplies the analytic-order,
  finite-product and logarithmic-derivative primitives used below.
* `AnalyticNumberTheory.ComplexAnalysis.LocalZeroProduct` already packages the finite zero-product
  algebra and local finite-order factorization needed here.
* Fresh searches of canonical same-revision `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`
  and exact-same-pin `subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`
  found no competing packaged regularized finite-zero quotient / `logDeriv` split layer.

Only the bounded quotient algebra is extracted. Quantitative growth transfer, Dirichlet objects,
GRH, contour arguments and application parameters are deliberately excluded.
-/

import AnalyticNumberTheory.ComplexAnalysis.LocalZeroProduct
import Mathlib.Tactic

open Complex Set Filter
open Classical
open scoped Topology

namespace AnalyticNumberTheory.ComplexAnalysis

noncomputable section

noncomputable def zeroFactorValue (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if hA : AnalyticAt ℂ f z then
    if hO : analyticOrderAt f z ≠ ⊤ then
      (hA.analyticOrderAt_ne_top.mp hO).choose z
    else 0
  else 0

theorem zeroFactorValue_spec
    {R : ℝ} {f : ℂ → ℂ} {ρ : ℂ}
    (hR : R < 1)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf0 : f 0 ≠ 0)
    (hρ : ρ ∈ SetOfZeros R f) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧ zeroFactorValue f ρ = g ρ ∧
      f =ᶠ[𝓝 ρ] fun z => (z - ρ) ^ analyticOrderNatAt f ρ * g z := by
  have hzero : 0 ∈ Metric.closedBall (0 : ℂ) 1 := by simp
  have hρball : ρ ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
    exact hρ.1.trans hR.le
  have horder0 : analyticOrderAt f 0 = 0 := by
    rw [analyticOrderAt_eq_zero]
    exact Or.inr hf0
  have hfinite : analyticOrderAt f ρ ≠ ⊤ := by
    apply hf.analyticOrderAt_ne_top_of_isPreconnected Metric.isPreconnected_closedBall hzero hρball
    rw [horder0]
    exact ENat.zero_ne_top
  have hanalytic : AnalyticAt ℂ f ρ := hf ρ hρball
  obtain ⟨hgAnalytic, hgNe, hfactor⟩ :=
    (hanalytic.analyticOrderAt_ne_top.mp hfinite).choose_spec
  let g : ℂ → ℂ := (hanalytic.analyticOrderAt_ne_top.mp hfinite).choose
  refine ⟨g, hgAnalytic, hgNe, ?_, ?_⟩
  · simp only [zeroFactorValue, hanalytic, ↓reduceDIte, ne_eq, hfinite, not_false_eq_true,
      smul_eq_mul, g]
  · simpa [smul_eq_mul, g] using hfactor

noncomputable def regularizedFiniteZeroQuotient (r : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if hfin : (SetOfZeros r f).Finite then
    if _ : z ∈ SetOfZeros r f then
      zeroFactorValue f z /
        ∏ ρ ∈ (hfin.toFinset \ {z}), (z - ρ) ^ analyticOrderNatAt f ρ
    else
      f z / ∏ ρ ∈ hfin.toFinset, (z - ρ) ^ analyticOrderNatAt f ρ
  else 1

theorem analyticOnNhd_regularizedFiniteZeroQuotient
    {r R : ℝ} {f : ℂ → ℂ}
    (hrR : r < R) (hR1 : R < 1)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf0 : f 0 ≠ 0) :
    AnalyticOnNhd ℂ (regularizedFiniteZeroQuotient r f) (Metric.closedBall (0 : ℂ) R) := by
  intro w hw
  unfold regularizedFiniteZeroQuotient
  by_cases hfinr : (SetOfZeros r f).Finite
  · simp only [hfinr, ↓reduceDIte]
    by_cases hmem : w ∈ SetOfZeros r f
    · obtain ⟨g, hgAnalytic, hgNe, hvalue, hlocal⟩ :=
        zeroFactorValue_spec (hrR.trans hR1) hf hf0 hmem
      have heq : ∀ᶠ z in 𝓝 w,
          (if h : z ∈ SetOfZeros r f then
              zeroFactorValue f z /
                ∏ ρ ∈ hfinr.toFinset \ {z}, (z - ρ) ^ analyticOrderNatAt f ρ
            else
              f z / ∏ ρ ∈ hfinr.toFinset, (z - ρ) ^ analyticOrderNatAt f ρ) =
            g z / ∏ ρ ∈ hfinr.toFinset \ {w}, (z - ρ) ^ analyticOrderNatAt f ρ := by
        filter_upwards [hlocal, hgAnalytic.continuousAt.eventually_ne hgNe] with z hz hzNe
        by_cases hzw : z = w
        · subst hzw
          rw [dif_pos hmem, hvalue]
        · have hznot : z ∉ SetOfZeros r f := by
            intro hzmem
            have hfz : f z = 0 := hzmem.2
            rw [hz] at hfz
            exact absurd hfz (mul_ne_zero (pow_ne_zero _ (sub_ne_zero_of_ne hzw)) hzNe)
          rw [dif_neg hznot, hz]
          have hwfin : w ∈ hfinr.toFinset := hfinr.mem_toFinset.mpr hmem
          rw [Finset.prod_eq_prod_sdiff_singleton_mul hwfin
            (fun ρ => (z - ρ) ^ analyticOrderNatAt f ρ)]
          rw [mul_comm ((z - w) ^ analyticOrderNatAt f w) (g z)]
          rw [mul_div_mul_right _ _ (pow_ne_zero _ (sub_ne_zero_of_ne hzw))]
      apply hgAnalytic.div _ _ |> fun h => h.congr _
      · use fun z => ∏ ρ ∈ hfinr.toFinset \ {w}, (z - ρ) ^ analyticOrderNatAt f ρ
      · exact analyticAt_finsetProd_sub_pow (hfinr.toFinset \ {w}) (analyticOrderNatAt f) w
      · refine Finset.prod_ne_zero_iff.mpr ?_
        intro x hx
        rw [Finset.mem_sdiff, Finset.mem_singleton] at hx
        exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hx.2))
      · filter_upwards [heq] with z hz using hz.symm
    · apply AnalyticAt.congr _ _
      · exact fun z => f z / ∏ ρ ∈ hfinr.toFinset, (z - ρ) ^ analyticOrderNatAt f ρ
      · refine AnalyticAt.div ?_ ?_ ?_
        · exact hf w (Metric.mem_closedBall.mpr <| le_trans hw.out hR1.le)
        · exact analyticAt_finsetProd_sub_pow hfinr.toFinset (analyticOrderNatAt f) w
        · refine Finset.prod_ne_zero_iff.mpr ?_
          intro x hx
          have hxmem := hfinr.mem_toFinset.mp hx
          have hne : w ≠ x := by
            rintro rfl
            exact hmem hxmem
          exact pow_ne_zero _ (sub_ne_zero.mpr hne)
      · filter_upwards [IsOpen.mem_nhds (isOpen_compl_iff.mpr hfinr.isClosed) hmem] with z hz
        split_ifs with h
        · exact absurd h hz
        · rfl
  · simp only [hfinr, ↓reduceDIte]
    exact analyticAt_const

theorem regularizedFiniteZeroQuotient_ne_zero
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf0 : f 0 ≠ 0) {r : ℝ} (hr1 : r < 1)
    (hfin : (SetOfZeros 1 f).Finite)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    regularizedFiniteZeroQuotient r f z ≠ 0 := by
  have hfinr := finiteSetOfZeros_mono hr1.le hfin
  by_cases hmem : z ∈ SetOfZeros r f
  · obtain ⟨g, _, hgNe, hvalue, _⟩ := zeroFactorValue_spec hr1 hf hf0 hmem
    unfold regularizedFiniteZeroQuotient
    rw [dif_pos hfinr, dif_pos hmem, hvalue]
    apply div_ne_zero hgNe
    refine Finset.prod_ne_zero_iff.mpr fun ρ hρ => ?_
    have hne : z ≠ ρ := by
      intro h
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hρ
      exact hρ.2 h.symm
    exact pow_ne_zero _ (sub_ne_zero.mpr hne)
  · unfold regularizedFiniteZeroQuotient
    rw [dif_pos hfinr, dif_neg hmem]
    have hfz : f z ≠ 0 := by
      intro h
      exact hmem ⟨hz, h⟩
    apply div_ne_zero hfz
    refine Finset.prod_ne_zero_iff.mpr fun ρ hρ => ?_
    have hρmem := hfinr.mem_toFinset.mp hρ
    have hne : z ≠ ρ := by
      rintro rfl
      exact hmem hρmem
    exact pow_ne_zero _ (sub_ne_zero.mpr hne)

theorem eq_zeroProduct_mul_regularizedFiniteZeroQuotient
    {f : ℂ → ℂ} {r : ℝ} (hr1 : r < 1)
    (hfin : (SetOfZeros 1 f).Finite)
    {z : ℂ} (hz : z ∉ SetOfZeros r f) :
    f z =
      (∏ ρ ∈ (finiteSetOfZeros_mono hr1.le hfin).toFinset,
        (z - ρ) ^ analyticOrderNatAt f ρ) * regularizedFiniteZeroQuotient r f z := by
  have hfinr := finiteSetOfZeros_mono hr1.le hfin
  unfold regularizedFiniteZeroQuotient
  rw [dif_pos hfinr, dif_neg hz]
  rw [mul_div_cancel₀]
  refine Finset.prod_ne_zero_iff.mpr fun ρ hρ => ?_
  have hρmem := hfinr.mem_toFinset.mp hρ
  have hne : z ≠ ρ := by
    rintro rfl
    exact hz hρmem
  exact pow_ne_zero _ (sub_ne_zero.mpr hne)

theorem logDeriv_eq_zeroSum_add_regularized
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf0 : f 0 ≠ 0) {r : ℝ} (hr1 : r < 1)
    (hfin : (SetOfZeros 1 f).Finite)
    {z : ℂ} (hz : ‖z‖ < r) (hfz : f z ≠ 0) :
    logDeriv f z =
      (∑ ρ ∈ (finiteSetOfZeros_mono hr1.le hfin).toFinset,
        (analyticOrderNatAt f ρ : ℂ) / (z - ρ)) +
      logDeriv (regularizedFiniteZeroQuotient r f) z := by
  have hfinr := finiteSetOfZeros_mono hr1.le hfin
  set P0 : ℂ → ℂ :=
    fun w => ∏ ρ ∈ hfinr.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ with hP0
  have hU : IsOpen (Metric.ball (0 : ℂ) r \ SetOfZeros r f) :=
    Metric.isOpen_ball.sdiff hfinr.isClosed
  have hzU : z ∈ Metric.ball (0 : ℂ) r \ SetOfZeros r f :=
    ⟨mem_ball_zero_iff.mpr hz, fun h => hfz h.2⟩
  have heq : f =ᶠ[𝓝 z] fun w => P0 w * regularizedFiniteZeroQuotient r f w := by
    filter_upwards [hU.mem_nhds hzU] with w hw
    exact eq_zeroProduct_mul_regularizedFiniteZeroQuotient hr1 hfin hw.2
  have hzne : ∀ ρ ∈ hfinr.toFinset, z ≠ ρ := by
    intro ρ hρ
    rintro rfl
    exact hfz (hfinr.mem_toFinset.mp hρ).2
  have hP0z : P0 z ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
      pow_ne_zero _ (sub_ne_zero.mpr (hzne ρ hρ))
  have hQz : regularizedFiniteZeroQuotient r f z ≠ 0 :=
    regularizedFiniteZeroQuotient_ne_zero hf hf0 hr1 hfin hz.le
  have hdP0 : DifferentiableAt ℂ P0 z :=
    DifferentiableAt.fun_finsetProd fun ρ _ =>
      ((differentiable_id.sub_const ρ).differentiableAt).pow _
  have hdQ : DifferentiableAt ℂ (regularizedFiniteZeroQuotient r f) z := by
    have hR : r < (r + 1) / 2 := by linarith
    have hR1 : (r + 1) / 2 < 1 := by linarith
    exact ((analyticOnNhd_regularizedFiniteZeroQuotient hR hR1 hf hf0) z (by
      rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
      calc
        ‖z‖ ≤ r := hz.le
        _ ≤ (r + 1) / 2 := by linarith)).differentiableAt
  calc
    logDeriv f z = logDeriv (fun w => P0 w * regularizedFiniteZeroQuotient r f w) z := by
      unfold logDeriv
      simp only [Pi.div_apply]
      rw [heq.deriv_eq, heq.eq_of_nhds]
    _ = logDeriv P0 z + logDeriv (regularizedFiniteZeroQuotient r f) z :=
      logDeriv_mul z hP0z hQz hdP0 hdQ
    _ = _ := by
      rw [hP0, logDeriv_finsetProd_sub_pow hzne]

end

end AnalyticNumberTheory.ComplexAnalysis
