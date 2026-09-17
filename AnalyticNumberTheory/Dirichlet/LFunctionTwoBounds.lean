import AnalyticNumberTheory.Dirichlet.LFunctionGrowthUniform
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Dirichlet L-function bounds on `Re s ≥ 2`

This file records the q-uniform Jensen-centre lower bound needed by local
Dirichlet zero-count arguments.

External source audit:

* `PalomarArchive/anthropics--zeta-23-lean--94784dd69547`
  at commit `cec57f919ccf34e5fa5372b4ba332f7c848bbb6e`,
  `Zeta23/ThmE/LGrowth.lean`, declarations
  `norm_LFunction_sub_one_le`, `LFunction_lower_bound_two`, and
  `LFunction_ne_zero_of_two_le_re`;
* pinned Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` already supplies the
  Dirichlet `LSeries` convergence/identification API and `hasSum_zeta_two`;
* canonical same-revision `subfish-zhou/goldbach-lean` contains no packaged
  theorem with this Jensen-centre interface.

The zeta-23 repository uses a different Mathlib revision, so no module is
imported wholesale.  The neutral proof is rechecked here against ANT's pinned
revision.  No GRH, primitivity, or project-specific hypothesis is used.
-/

open Complex DirichletCharacter

namespace AnalyticNumberTheory.Dirichlet

noncomputable section

/-- On `Re s ≥ 2`, a Dirichlet L-function is within `π²/6 - 1` of `1`.
The bound is uniform in the modulus and the character. -/
theorem norm_LFunction_sub_one_le_of_two_le_re
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 2 ≤ s.re) :
    ‖χ.LFunction s - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by
  have hs1 : 1 < s.re := by linarith
  rw [LFunction_eq_LSeries χ hs1]
  set f : ℕ → ℂ := fun n => χ (n : ZMod q) with hf
  have hsum : Summable (LSeries.term f s) := LSeriesSummable_of_one_lt_re χ hs1
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have h01 : ∑ i ∈ Finset.range 2, LSeries.term f s i = 1 := by
    simp [Finset.sum_range_succ, LSeries.term, hf]
  have hL : LSeries f s - 1 = ∑' i, LSeries.term f s (i + 2) := by
    rw [LSeries, ← hsplit, h01]
    ring
  rw [hL]
  have hle : ∀ i : ℕ, ‖LSeries.term f s (i + 2)‖ ≤ 1 / ((i : ℝ) + 2) ^ 2 := by
    intro i
    have hpos : 0 < i + 2 := by omega
    rw [LSeries.term_of_ne_zero (by omega : i + 2 ≠ 0), norm_div,
      Complex.norm_natCast_cpow_of_pos hpos]
    have h1 : ‖f (i + 2)‖ ≤ 1 := χ.norm_le_one _
    have hbase : (1 : ℝ) ≤ ((i + 2 : ℕ) : ℝ) := by exact_mod_cast hpos
    have hpow : ((i + 2 : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((i + 2 : ℕ) : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le hbase hs
    rw [Real.rpow_two] at hpow
    have h2pos : (0 : ℝ) < ((i + 2 : ℕ) : ℝ) ^ 2 := by positivity
    have hσpos : (0 : ℝ) < ((i + 2 : ℕ) : ℝ) ^ s.re := by positivity
    calc
      ‖f (i + 2)‖ / ((i + 2 : ℕ) : ℝ) ^ s.re
          ≤ 1 / ((i + 2 : ℕ) : ℝ) ^ s.re :=
        div_le_div_of_nonneg_right h1 hσpos.le
      _ ≤ 1 / ((i + 2 : ℕ) : ℝ) ^ 2 := one_div_le_one_div_of_le h2pos hpow
      _ = 1 / ((i : ℝ) + 2) ^ 2 := by push_cast; ring
  have htwo : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2)
      (Real.pi ^ 2 / 6 - 1) := by
    have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    norm_num [Finset.sum_range_succ] at h
    exact h.congr_fun fun n => by ring
  have hsum' : Summable (fun i => LSeries.term f s (i + 2)) :=
    (summable_nat_add_iff 2).mpr hsum
  calc
    ‖∑' i, LSeries.term f s (i + 2)‖ ≤ ∑' i, ‖LSeries.term f s (i + 2)‖ :=
      norm_tsum_le_tsum_norm hsum'.norm
    _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ 2 :=
      hsum'.norm.tsum_le_tsum hle htwo.summable
    _ = Real.pi ^ 2 / 6 - 1 := htwo.tsum_eq

/-- Uniform Jensen-centre lower bound: every Dirichlet L-function has norm at
least `1/3` on `Re s ≥ 2`. -/
theorem one_third_le_norm_LFunction_of_two_le_re
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 2 ≤ s.re) :
    (1 / 3 : ℝ) ≤ ‖χ.LFunction s‖ := by
  have h := norm_LFunction_sub_one_le_of_two_le_re χ hs
  have h' : ‖(1 : ℂ)‖ - ‖1 - χ.LFunction s‖ ≤ ‖χ.LFunction s‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) (1 - χ.LFunction s)
  rw [norm_sub_rev] at h'
  simp only [norm_one] at h'
  have hpi := Real.pi_lt_d2
  nlinarith [Real.pi_pos]

/-- In particular, Dirichlet L-functions do not vanish on `Re s ≥ 2`. -/
theorem LFunction_ne_zero_of_two_le_re
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 2 ≤ s.re) :
    χ.LFunction s ≠ 0 := by
  intro hzero
  have h := one_third_le_norm_LFunction_of_two_le_re χ hs
  rw [hzero, norm_zero] at h
  norm_num at h

end

end AnalyticNumberTheory.Dirichlet
