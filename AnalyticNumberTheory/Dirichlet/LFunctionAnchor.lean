import AnalyticNumberTheory.Dirichlet.LFunctionGrowth
import AnalyticNumberTheory.Dirichlet.RightHalfPlaneBounds
import AnalyticNumberTheory.Dirichlet.LocalLogDerivative

/-!
# Quantitative anchor bounds for Dirichlet L-functions

This module extracts the project-neutral Dirichlet-L anchor estimates used by
the existing finite-rectangle logarithmic-derivative formalization.

Provenance: adapted from
`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`,
`MathlibNt/AnalyticNumberTheory/DirichletL/DirichletLZeroFreeHalfPlaneLogDerivative.lean`.

The lower anchor reuses Mathlib's existing
`DirichletCharacter.norm_LFunction_product_ge_one`; it is not reimplemented in
ANT.  The upper bounds reuse ANT's already-verified conditional-series growth
and right-half-plane majorant layers.
-/

open Complex Metric Set
open scoped Topology

namespace AnalyticNumberTheory.Dirichlet

noncomputable section

/-- Absolute-convergence/product anchor: at real part `1 + δ/2`, every
Dirichlet character has norm at least `δ/4` when `0 < δ ≤ 1/2`. -/
theorem delta_quarter_le_norm_LFunction_anchor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (t : ℝ) : δ / 4 ≤ ‖χ.LFunction ((1 + δ / 2 : ℝ) + I * t)‖ := by
  let K : ℝ := 4 / δ
  have hK : 0 < K := by dsimp [K]; positivity
  have hbound : 1 + 1 / ((1 + δ / 2) - 1) ≤ K := by
    dsimp [K]
    rw [show (1 + δ / 2) - 1 = δ / 2 by ring]
    field_simp
    nlinarith
  have htriv : ‖DirichletCharacter.LFunctionTrivChar q (1 + (δ / 2 : ℂ))‖ ≤ K := by
    have h := norm_dirichletLFunction_le (1 : DirichletCharacter ℂ q)
      (1 + δ / 2) 0 (by linarith)
    simpa [DirichletCharacter.LFunctionTrivChar] using h.trans hbound
  have hsq : ‖(χ ^ 2).LFunction (1 + (δ / 2 : ℂ) + 2 * I * t)‖ ≤ K := by
    have h := norm_dirichletLFunction_le (χ ^ 2) (1 + δ / 2) (2 * t) (by linarith)
    convert h.trans hbound using 1 <;> push_cast <;> congr 2
    ring
  have hp := χ.norm_LFunction_product_ge_one (by positivity : 0 < δ / 2) t
  simp only [norm_mul, norm_pow] at hp
  have hmajor : 1 ≤ K ^ 3 * ‖χ.LFunction ((1 + δ / 2 : ℝ) + I * t)‖ ^ 4 * K := by
    refine hp.trans ?_
    push_cast
    gcongr
  by_contra hn
  have hn' : ‖χ.LFunction ((1 + δ / 2 : ℝ) + I * t)‖ < δ / 4 := lt_of_not_ge hn
  have hsmall : K ^ 3 * ‖χ.LFunction ((1 + δ / 2 : ℝ) + I * t)‖ ^ 4 * K <
      K ^ 3 * (δ / 4) ^ 4 * K := by
    gcongr
  have hid : K ^ 3 * (δ / 4) ^ 4 * K = 1 := by
    dsimp [K]
    field_simp
  exact (not_lt_of_ge hmajor) (hsmall.trans_eq hid)

/-- The standard anchor disk centered at `1 + δ/2 + it` stays to the right of
`1 - δ`. -/
lemma anchor_disk_re_lower {δ : ℝ} (_hδ : 0 < δ) (t : ℝ) {w : ℂ}
    (hw : w ∈ ball ((1 + δ / 2 : ℝ) + I * t) (3 * δ / 2)) :
    1 - δ < w.re := by
  have hn : ‖w - ((1 + δ / 2 : ℝ) + I * t)‖ < 3 * δ / 2 := by
    simpa only [mem_ball, dist_eq_norm] using hw
  have hl := (abs_le.mp (Complex.abs_re_le_norm
    (w - ((1 + δ / 2 : ℝ) + I * t)))).1
  simp only [sub_re, add_re, ofReal_re, mul_re, I_re, zero_mul,
    I_im, ofReal_im, mul_zero, sub_zero, add_zero] at hl
  linarith

/-- Linear-in-height upper bound on the standard anchor disk, obtained from the
nonprincipal conditional-series growth theorem. -/
theorem norm_LFunction_le_on_anchor_disk {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (t : ℝ) {w : ℂ}
    (hw : w ∈ ball ((1 + δ / 2 : ℝ) + I * t) (3 * δ / 2)) :
    ‖χ.LFunction w‖ ≤ 8 * q * (1 + |t|) := by
  have hre := anchor_disk_re_lower hδ t hw
  have hwpos : 0 < w.re := by linarith
  have hwhalf : (1 : ℝ) / 2 ≤ w.re := by linarith
  have hn : ‖w - ((1 + δ / 2 : ℝ) + I * t)‖ < 3 * δ / 2 := by
    simpa only [mem_ball, dist_eq_norm] using hw
  have ha : ‖((1 + δ / 2 : ℝ) : ℂ) + I * t‖ ≤ 1 + δ / 2 + |t| := by
    calc
      _ ≤ ‖((1 + δ / 2 : ℝ) : ℂ)‖ + ‖I * (t : ℂ)‖ := norm_add_le _ _
      _ = _ := by
        simp only [norm_real, Real.norm_eq_abs, norm_mul, norm_I, one_mul]
        rw [abs_of_pos (by linarith : 0 < 1 + δ / 2)]
  have hwnorm : ‖w‖ ≤ 2 + |t| := by
    have ht : ‖w‖ ≤ ‖w - ((1 + δ / 2 : ℝ) + I * t)‖ +
        ‖((1 + δ / 2 : ℝ) : ℂ) + I * t‖ := by
      simpa only [sub_add_cancel] using
        norm_add_le (w - ((1 + δ / 2 : ℝ) + I * t)) ((1 + δ / 2 : ℝ) + I * t)
    linarith only [ht, hn, ha, hδ1]
  have hdiv : ‖w‖ / w.re ≤ 2 * ‖w‖ := by
    apply (div_le_iff₀ hwpos).2
    nlinarith [norm_nonneg w]
  calc
    _ ≤ q * (1 + ‖w‖ / w.re) := norm_LFunction_le_growth χ hχ w hwpos
    _ ≤ q * (8 * (1 + |t|)) := by
      gcongr
      nlinarith [abs_nonneg t]
    _ = _ := by ring

end

end AnalyticNumberTheory.Dirichlet
