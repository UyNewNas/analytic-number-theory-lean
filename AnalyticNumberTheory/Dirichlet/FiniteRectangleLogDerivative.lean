import AnalyticNumberTheory.Dirichlet.LFunctionAnchor

/-!
# Finite-rectangle logarithmic-derivative estimate for Dirichlet L-functions

This module is a provenance-preserving adaptation of the already-formalized
finite-rectangle theorem in
`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`,
`MathlibNt/AnalyticNumberTheory/DirichletL/DirichletLZeroFreeFiniteRectangleLogDerivative.lean`.

The proof deliberately reuses ANT's extracted neutral layers:

* `norm_logDeriv_le_small_disk` for the generic local complex analysis;
* `norm_LFunction_le_on_anchor_disk` for growth on the anchor disk;
* `delta_quarter_le_norm_LFunction_anchor` for the lower anchor.

Only finite-rectangle nonvanishing is assumed.  No GRH, Goldbach, Mangerel, or
downstream application statement is built into this theorem.

The upstream source states the width restriction as `δ ≤ 1/4`.  The same proof
geometry and anchor estimates remain valid through `δ ≤ 1/2`: the anchor disk
still lies in `1-δ < Re s < 2`, stays in `Re s > 1/2`, and has imaginary-radius
less than one.  The open lower edge is exposed explicitly because at the
endpoint `δ = 1/2` a GRH consumer may have zeros on `Re s = 1/2` even though
the actual anchor disk lies strictly to its right.
-/

open Complex Metric Set

namespace AnalyticNumberTheory.Dirichlet

noncomputable section

/-- The standard anchor disk lies in the finite enlarged rectangle used by the
quantitative logarithmic-derivative argument. -/
theorem anchor_disk_subset_rectangle {δ T t : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (ht : |t| ≤ T) {w : ℂ}
    (hw : w ∈ ball ((1 + δ / 2 : ℝ) + I * t) (3 * δ / 2)) :
    1 - δ ≤ w.re ∧ w.re ≤ 2 ∧ |w.im| ≤ T + 1 := by
  have hn : ‖w - ((1 + δ / 2 : ℝ) + I * t)‖ < 3 * δ / 2 := by
    simpa only [mem_ball, dist_eq_norm] using hw
  have hre := (abs_le.mp (Complex.abs_re_le_norm
    (w - ((1 + δ / 2 : ℝ) + I * t)))).2
  have him := Complex.abs_im_le_norm (w - ((1 + δ / 2 : ℝ) + I * t))
  simp only [sub_re, add_re, ofReal_re, mul_re, I_re, zero_mul,
    I_im, ofReal_im, mul_zero, sub_zero, add_zero] at hre
  simp only [sub_im, add_im, ofReal_im, mul_im, I_re, zero_mul,
    I_im, ofReal_re, one_mul, zero_add] at him
  refine ⟨(anchor_disk_re_lower hδ t hw).le, ?_, ?_⟩
  · linarith only [hre, hn, hδ1]
  · calc
      |w.im| ≤ |w.im - t| + |t| := by
        simpa only [sub_add_cancel] using abs_add_le (w.im - t) t
      _ ≤ 3 * δ / 2 + T := add_le_add (him.trans hn.le) ht
      _ ≤ T + 1 := by linarith only [hδ1]

/-- Effective logarithmic derivative from zero-freeness on a finite rectangle
whose lower real-part edge is open.

For `0 < δ ≤ 1/2`, it is enough that `L(s,χ)` be nonzero for
`1-δ < Re(s) ≤ 2`, `|Im(s)| ≤ T+1`.  The strict lower edge matches the actual
open anchor disk and is important at `δ = 1/2`, where applications may have
zeros exactly on `Re s = 1/2`.
-/
theorem norm_logDeriv_LFunction_le_of_zeroFree_openLowerRectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {δ T : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (_hT : 0 ≤ T)
    (hzero : ∀ z : ℂ, 1 - δ < z.re → z.re ≤ 2 → |z.im| ≤ T + 1 →
      χ.LFunction z ≠ 0)
    (t β : ℝ) (ht : |t| ≤ T) (hβlo : 1 - δ / 2 ≤ β) (hβhi : β ≤ 1 + δ) :
    ‖logDeriv χ.LFunction ((β : ℂ) + I * t)‖ ≤
      40 / δ * Real.log (32 * q * (1 + |t|) / δ) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hbB : δ / 4 < 8 * q * (1 + |t|) := by
    have hprod : (1 : ℝ) ≤ q * (1 + |t|) := by
      nlinarith [abs_nonneg t]
    nlinarith
  have hz : dist ((β : ℂ) + I * t) ((1 + δ / 2 : ℝ) + I * t) ≤ δ := by
    rw [dist_add_right, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hzero_disk : ∀ w ∈ ball ((1 + δ / 2 : ℝ) + I * t) (3 * δ / 2),
      χ.LFunction w ≠ 0 := by
    intro w hw
    have hlo : 1 - δ < w.re := anchor_disk_re_lower hδ t hw
    obtain ⟨_hlo, hhi, him⟩ := anchor_disk_subset_rectangle hδ hδ1 ht hw
    exact hzero w hlo hhi him
  have h := norm_logDeriv_le_small_disk χ.LFunction
    ((1 + δ / 2 : ℝ) + I * t) ((β : ℂ) + I * t) hδ
    (by positivity : 0 < δ / 4) hbB (χ.differentiable_LFunction hχ).differentiableOn
    hzero_disk
    (fun w hw ↦ norm_LFunction_le_on_anchor_disk χ hχ hδ hδ1 t hw)
    (delta_quarter_le_norm_LFunction_anchor χ hδ hδ1 t) hz
  have harg : (8 * (q : ℝ) * (1 + |t|)) / (δ / 4) =
      32 * q * (1 + |t|) / δ := by ring
  rw [harg] at h
  convert h using 1
  ring

/-- Effective logarithmic derivative from zero-freeness on one finite closed
rectangle.  This compatibility wrapper preserves the previous API shape while
using the wider `δ ≤ 1/2` range. -/
theorem norm_logDeriv_LFunction_le_of_zeroFree_rectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {δ T : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hT : 0 ≤ T)
    (hzero : ∀ z : ℂ, 1 - δ ≤ z.re → z.re ≤ 2 → |z.im| ≤ T + 1 →
      χ.LFunction z ≠ 0)
    (t β : ℝ) (ht : |t| ≤ T) (hβlo : 1 - δ / 2 ≤ β) (hβhi : β ≤ 1 + δ) :
    ‖logDeriv χ.LFunction ((β : ℂ) + I * t)‖ ≤
      40 / δ * Real.log (32 * q * (1 + |t|) / δ) := by
  exact norm_logDeriv_LFunction_le_of_zeroFree_openLowerRectangle
    χ hχ hδ hδ1 hT
    (fun z hzlo hzhi hzim ↦ hzero z hzlo.le hzhi hzim)
    t β ht hβlo hβhi

end

end AnalyticNumberTheory.Dirichlet
