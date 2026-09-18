import Mathlib.Data.Real.Basic

/-!
# RH 塔程序——CNV 1986 代数核（IL(1) ⟺ γ-Turán，13 号）

IL(1) ⟺ γ(n+1)² > γ(n)γ(n+2)（CNV 1986）。
代数核：比率 r_m = γ(m+1)/γ(m) 单调 ⟺ γ 对数凸（b² ≥ ac）。
-/

namespace RiemannEssence

-- b/a ≤ c/b ⟺ b² ≤ a·c（a,b > 0）——比率单调 ⟺ 对数凸
lemma ratio_mono_iff_log_convex {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) :
    b / a ≤ c / b ↔ b ^ 2 ≤ a * c := by
  rw [div_le_div_iff ha hb]
  nlinarith

-- 严格版本
lemma ratio_mono_strict_iff_log_convex {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) :
    b / a < c / b ↔ b ^ 2 < a * c := by
  rw [div_lt_div_iff ha hb]
  nlinarith

-- γ-Turán 的等价形式：γ(n+1)² > γ(n)γ(n+2) ⟺ r_{n+1} > r_n（γ 正）
lemma turan_iff_ratio {g₀ g₁ g₂ : ℝ} (hg₀ : 0 < g₀) (hg₁ : 0 < g₁) :
    g₁ ^ 2 > g₀ * g₂ ↔ g₁ / g₀ < g₂ / g₁ := by
  rw [div_lt_div_iff hg₀ hg₁]
  nlinarith

end RiemannEssence
