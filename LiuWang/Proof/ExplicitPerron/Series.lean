import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Perron.Main
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.Basic

/-!
# Finite Perron integration at real endpoints

Adapted from
`subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`,
`LiuWang/Proof/ExplicitPerron/Series.lean`.

The mathematical declarations and proofs are preserved.  The only source-level
adaptation is the import boundary: the upstream character-specialized
`PerronSeries.Interchange` import is replaced by the direct Mathlib imports
actually used by this generic coefficient-sequence layer.

The natural-indexed L-series convention explicitly omits index zero. No
assumption on the value of the totalized complex power at zero is used.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LiuWang.Proof.ExplicitPerron

open BombieriVinogradov.SiegelWalfisz

def vertical (f : ℂ → ℂ) (b lo hi : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ u in lo..hi, f (b + u * Complex.I)

theorem vertical_eq_VIntegral' (f : ℂ → ℂ) (b lo hi : ℝ) :
    vertical f b lo hi = VIntegral' f b lo hi := by
  simp only [vertical, VIntegral', VIntegral, smul_eq_mul]
  field_simp
  simp [mul_comm]

def seriesIntegrand (a : ℕ → ℂ) (x : ℝ) (s : ℂ) : ℂ :=
  LSeries a s * ((x : ℂ) ^ s / s)

def term (a : ℕ → ℂ) (x : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  LSeries.term a s n * ((x : ℂ) ^ s / s)

def scalarTerm (a : ℕ → ℂ) (x b T : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else a n * truncatedPerronKernel (x / n) b T

def stepTerm (a : ℕ → ℂ) (x : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else a n * (perronStepWeight (x / n) : ℂ)

def majorant (a : ℕ → ℂ) (x b T : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    ‖a n‖ * (if x / n = 1 then b / (Real.pi * T)
      else (x / n) ^ b * min 1 (1 / (Real.pi * T * |Real.log (x / n)|)))

theorem line_ne_zero {b : ℝ} (hb : 0 < b) (u : ℝ) :
    (b : ℂ) + u * Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem term_continuous (a : ℕ → ℂ) {x b : ℝ}
    (hx : 0 < x) (hb : 0 < b) (n : ℕ) :
    Continuous (fun u : ℝ => term a x n (b + u * Complex.I)) := by
  by_cases hn : n = 0
  · subst n
    simpa [term, LSeries.term_def] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hp : Continuous (fun u : ℝ => (b : ℂ) + u * Complex.I) := by fun_prop
  simp only [term, LSeries.term_def, hn, if_false]
  exact (continuous_const.div (hp.const_cpow (Or.inl hnC))
    (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hnC))).mul
    ((hp.const_cpow (Or.inl hxC)).div hp (line_ne_zero hb))

theorem norm_term_le (a : ℕ → ℂ) {x b : ℝ}
    (hx : 0 < x) (hb : 0 < b) (n : ℕ) (u : ℝ) :
    ‖term a x n (b + u * Complex.I)‖ ≤
      (x ^ b / b) * ‖LSeries.term a (b : ℂ) n‖ := by
  by_cases hn : n = 0
  · subst n
    simp [term, LSeries.term_def]
  have hr : ((b : ℂ) + u * Complex.I).re = b := by simp
  have hnorm : b ≤ ‖(b : ℂ) + u * Complex.I‖ := by
    simpa [abs_of_pos hb] using Complex.abs_re_le_norm ((b : ℂ) + u * Complex.I)
  simp only [term, LSeries.term_def, hn, if_false, norm_mul, norm_div]
  rw [Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa using hb.ne'),
    Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa using hb.ne')]
  simp only [hr, Complex.ofReal_re]
  calc
    ‖a n‖ / (n : ℝ) ^ b * (x ^ b / ‖(b : ℂ) + u * Complex.I‖) ≤
        ‖a n‖ / (n : ℝ) ^ b * (x ^ b / b) := by gcongr
    _ = _ := by ring

def termMap (a : ℕ → ℂ) {x b : ℝ} (hx : 0 < x) (hb : 0 < b)
    (n : ℕ) : C(ℝ, ℂ) :=
  ⟨_, term_continuous a hx hb n⟩

theorem summable_termMap (a : ℕ → ℂ) {x b lo hi : ℝ}
    (hx : 0 < x) (hb : 0 < b) (ha : LSeriesSummable a (b : ℂ)) :
    Summable (fun n => ‖(termMap a hx hb n).restrict
      (TopologicalSpace.Compacts.mk (uIcc lo hi) isCompact_uIcc)‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (f := fun n => (x ^ b / b) * ‖LSeries.term a (b : ℂ) n‖)
  · intro n
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro u
    exact norm_term_le a hx hb n u.1
  · exact ha.norm.mul_left _

theorem vertical_term (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) (b T : ℝ) (n : ℕ) :
    vertical (term a x n) b (-T) T = scalarTerm a x b T n := by
  by_cases hn : n = 0
  · subst n
    simp [vertical, term, scalarTerm, LSeries.term_def]
  have heq : term a x n = fun s => a n * perronKernelIntegrand (x / n) s := by
    funext s
    simp only [term, LSeries.term_def, hn, if_false, perronKernelIntegrand,
      Complex.ofReal_div]
    rw [Complex.div_cpow_ofReal_nonneg hx.le (Nat.cast_nonneg n)]
    simp only [Complex.ofReal_natCast]
    ring
  rw [heq, scalarTerm, if_neg hn, vertical, intervalIntegral.integral_const_mul,
    truncatedPerronKernel, ← vertical_eq_VIntegral', vertical]
  ring

theorem vertical_eq_tsum (a : ℕ → ℂ) {x b T : ℝ}
    (hx : 0 < x) (hb : 0 < b) (ha : LSeriesSummable a (b : ℂ)) :
    vertical (seriesIntegrand a x) b (-T) T = ∑' n, scalarTerm a x b T n := by
  have h := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
    (summable_termMap a (lo := -T) (hi := T) hx hb ha)
  simp only [termMap, ContinuousMap.coe_mk] at h
  simp only [← vertical_term a hx, vertical]
  rw [tsum_mul_left, h]
  congr 2
  funext u
  simp only [seriesIntegrand, LSeries, term, tsum_mul_right]

theorem ratio_ne_one {x : ℝ} (hx : ∀ n : ℕ, x ≠ n) {n : ℕ} (hn : n ≠ 0) :
    x / n ≠ 1 := by
  exact fun h => hx n ((div_eq_one_iff_eq (by exact_mod_cast hn)).mp h)

theorem norm_scalar_sub_step_le (a : ℕ → ℂ) {x b T : ℝ}
    (hx : 0 < x) (hb : 0 < b) (hT : 0 < T) (n : ℕ) :
    ‖scalarTerm a x b T n - stepTerm a x n‖ ≤ majorant a x b T n := by
  by_cases hn : n = 0
  · simp [scalarTerm, stepTerm, majorant, hn]
  simp only [scalarTerm, stepTerm, majorant, hn, if_false, ← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_truncatedPerronKernel_sub_stepWeight_lt
      (div_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))) hb hT).le (norm_nonneg _)

theorem majorant_nonneg (a : ℕ → ℂ) {x b T : ℝ}
    (hx : 0 < x) (hb : 0 < b) (hT : 0 < T) (n : ℕ) : 0 ≤ majorant a x b T n := by
  unfold majorant
  split_ifs <;> positivity

theorem majorant_le_normTerm (a : ℕ → ℂ) {x b T : ℝ}
    (hx : 0 < x) (hxn : ∀ n : ℕ, x ≠ n) (hb : 0 < b) (n : ℕ) :
    majorant a x b T n ≤ x ^ b * ‖LSeries.term a (b : ℂ) n‖ := by
  by_cases hn : n = 0
  · simp [majorant, LSeries.term_def, hn]
  simp only [majorant, hn, if_false, ratio_ne_one hxn hn,
    LSeries.term_def, norm_div]
  rw [Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa using hb.ne')]
  simp only [Complex.ofReal_re]
  rw [Real.div_rpow hx.le (Nat.cast_nonneg n)]
  calc
    ‖a n‖ * (x ^ b / (n : ℝ) ^ b *
        min 1 (1 / (Real.pi * T * |Real.log (x / n)|))) ≤
      ‖a n‖ * (x ^ b / (n : ℝ) ^ b * 1) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
    _ = _ := by ring

theorem summable_majorant (a : ℕ → ℂ) {x b T : ℝ}
    (hx : 0 < x) (hxn : ∀ n : ℕ, x ≠ n) (hb : 0 < b) (hT : 0 < T)
    (ha : LSeriesSummable a (b : ℂ)) : Summable (majorant a x b T) :=
  Summable.of_nonneg_of_le (majorant_nonneg a hx hb hT)
    (majorant_le_normTerm a hx hxn hb) (ha.norm.mul_left _)

theorem stepTerm_eq (a : ℕ → ℂ) {x : ℝ} (hx : 0 ≤ x)
    (hxn : ∀ n : ℕ, x ≠ n) (n : ℕ) :
    stepTerm a x n = if n ∈ Finset.Icc 1 ⌊x⌋₊ then a n else 0 := by
  by_cases hn : n = 0
  · simp [stepTerm, hn]
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hratio := ratio_ne_one hxn hn
  simp only [stepTerm, hn, if_false, perronStepWeight, hratio]
  by_cases hnx : (n : ℝ) ≤ x
  · have hmem : n ∈ Finset.Icc 1 ⌊x⌋₊ :=
      Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn, (Nat.le_floor_iff hx).2 hnx⟩
    rw [if_neg (not_lt.mpr ((le_div_iff₀ hnpos).2 (by simpa using hnx))),
      if_pos hmem]
    simp
  · have hmem : n ∉ Finset.Icc 1 ⌊x⌋₊ := by
      intro h
      exact hnx ((Nat.le_floor_iff hx).1 (Finset.mem_Icc.mp h).2)
    rw [if_pos ((div_lt_one hnpos).2 (lt_of_not_ge hnx)), if_neg hmem]
    simp

theorem summable_stepTerm (a : ℕ → ℂ) {x : ℝ} (hx : 0 ≤ x)
    (hxn : ∀ n : ℕ, x ≠ n) : Summable (stepTerm a x) := by
  change Summable (fun n => stepTerm a x n)
  simp_rw [stepTerm_eq a hx hxn]
  exact summable_of_ne_finset_zero (s := Finset.Icc 1 ⌊x⌋₊)
    (fun n hn => if_neg hn)

theorem tsum_stepTerm (a : ℕ → ℂ) {x : ℝ} (hx : 0 ≤ x)
    (hxn : ∀ n : ℕ, x ≠ n) :
    ∑' n, stepTerm a x n = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n := by
  simp_rw [stepTerm_eq a hx hxn]
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn => if_neg hn)]
  exact Finset.sum_congr rfl (fun n hn => if_pos hn)

theorem norm_vertical_sub_sum_le (a : ℕ → ℂ) {x b T : ℝ}
    (hx : 0 < x) (hxn : ∀ n : ℕ, x ≠ n) (hb : 0 < b) (hT : 0 < T)
    (ha : LSeriesSummable a (b : ℂ)) :
    ‖vertical (seriesIntegrand a x) b (-T) T -
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n‖ ≤ ∑' n, majorant a x b T n := by
  have hm := summable_majorant a hx hxn hb hT ha
  have he := Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (norm_scalar_sub_step_le a hx hb hT) hm
  have hs := summable_stepTerm a hx.le hxn
  have hscalar : Summable (scalarTerm a x b T) := by
    simpa only [sub_add_cancel] using he.of_norm.add hs
  rw [vertical_eq_tsum a hx hb ha, ← tsum_stepTerm a hx.le hxn,
    ← hscalar.tsum_sub hs]
  exact (norm_tsum_le_tsum_norm he).trans
    (he.tsum_le_tsum (norm_scalar_sub_step_le a hx hb hT) hm)

end LiuWang.Proof.ExplicitPerron
