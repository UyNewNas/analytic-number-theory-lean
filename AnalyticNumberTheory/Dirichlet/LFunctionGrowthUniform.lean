import AnalyticNumberTheory.Dirichlet.LFunctionGrowth
import Mathlib.Tactic

/-!
# Uniform right-half-plane growth for Dirichlet L-functions

This file records the q-uniform linear growth seam used by local zero-count
arguments.

External source audit:
`anthropics/formal-math@fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`,
`zeta23/Zeta23/ThmE/LGrowth.lean`, theorem `LFunction_growth_right_uniform`.
The external repository pins a different Mathlib revision, so it is prior art,
not a drop-in dependency.  This proof reuses ANT's already-verified same-pin
`norm_LFunction_le_growth`; no second continuation framework is introduced.

Historical same-pin verification: the identical theorem body was compiled and
axiom-audited on ANT PR #76 before that long-lived integration lane diverged.
This module restores the neutral seam on current stable `main` for the named
Liouville-reflection consumer.
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
