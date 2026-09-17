import AnalyticNumberTheory.Dirichlet.LFunctionGrowth
import Mathlib.Tactic

/-!
# Uniform right-half-plane growth for Dirichlet L-functions

This file records the q-uniform linear growth seam used by local zero-count
arguments.

External source audit:
`PalomarArchive/anthropics--zeta-23-lean--94784dd69547`
at commit `cec57f919ccf34e5fa5372b4ba332f7c848bbb6e`,
`Zeta23/ThmE/LGrowth.lean`, theorem `LFunction_growth_right_uniform`.

The external repository pins a different mathlib revision, so the theorem is not
imported wholesale.  ANT already has the stronger-for-our-purpose neutral
half-plane estimate `norm_LFunction_le_growth`; only the numerical q-uniform
specialization needed by the Jensen/local-zero-count argument is proved here.
-/

open Complex

namespace AnalyticNumberTheory.Dirichlet

noncomputable section

/-- For every nonprincipal character, the actual Mathlib Dirichlet `L`-function
has an absolute q-uniform linear height bound on `Re s ≥ 0.15`.

The constant `8` and the shape match the zeta-23 local-zero-count input, while
the proof reuses ANT's already-verified conditional-series growth theorem. -/
theorem norm_LFunction_le_growth_right_uniform
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hσ : (0.15 : ℝ) ≤ s.re) :
    ‖χ.LFunction s‖ ≤ 8 * q * (|s.im| + 3) := by
  have hσpos : 0 < s.re := lt_of_lt_of_le (by norm_num) hσ
  have h := norm_LFunction_le_growth χ hχ s hσpos
  have hn : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_pos hσpos] at hn
  have h2 : 1 + ‖s‖ / s.re ≤ 2 + (0.15 : ℝ)⁻¹ * |s.im| := by
    calc
      1 + ‖s‖ / s.re ≤ 1 + (s.re + |s.im|) / s.re := by gcongr
      _ = 2 + |s.im| / s.re := by
        field_simp [ne_of_gt hσpos]
        ring
      _ ≤ 2 + |s.im| / (0.15 : ℝ) := by gcongr
      _ = 2 + (0.15 : ℝ)⁻¹ * |s.im| := by rw [div_eq_inv_mul]
  have hinside : 2 + (0.15 : ℝ)⁻¹ * |s.im| ≤ 8 * (|s.im| + 3) := by
    norm_num
    nlinarith [abs_nonneg s.im]
  calc
    ‖χ.LFunction s‖ ≤ q * (1 + ‖s‖ / s.re) := h
    _ ≤ q * (2 + (0.15 : ℝ)⁻¹ * |s.im|) := by gcongr
    _ ≤ q * (8 * (|s.im| + 3)) :=
      mul_le_mul_of_nonneg_left hinside (Nat.cast_nonneg q)
    _ = 8 * q * (|s.im| + 3) := by ring

end

end AnalyticNumberTheory.Dirichlet
