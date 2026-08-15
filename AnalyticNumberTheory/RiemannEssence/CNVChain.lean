import Mathlib.Data.Real.Basic

/-!
# RH 塔程序——CNV 完整链：r 递减 ⟹ γ-Turán（IL(1)，13 号）

r_m = γ(m+1)/γ(m)。r 递减（r₁ < r₀）⟹ γ(n+1)² > γ(n)γ(n+2)（CNV 1986）。
-/

namespace RiemannEssence

-- r 递减 ⟹ γ-Turán（r₀ = g₁/g₀, r₁ = g₂/g₁）
lemma cnv_turan {g₀ g₁ g₂ r₀ r₁ : ℝ} (hg₀ : 0 < g₀) (hg₁ : 0 < g₁)
    (hr₀ : r₀ = g₁ / g₀) (hr₁ : r₁ = g₂ / g₁) (hdec : r₁ < r₀) :
    g₀ * g₂ < g₁ ^ 2 := by
  subst hr₀
  subst hr₁
  -- g₂/g₁ < g₁/g₀ ⟺ g₀g₂ < g₁²
  rw [div_lt_div_iff hg₀ hg₁]
  nlinarith

-- r 非增版本
lemma cnv_turan_mono {g₀ g₁ g₂ r₀ r₁ : ℝ} (hg₀ : 0 < g₀) (hg₁ : 0 < g₁)
    (hr₀ : r₀ = g₁ / g₀) (hr₁ : r₁ = g₂ / g₁) (hdec : r₁ ≤ r₀) :
    g₀ * g₂ ≤ g₁ ^ 2 := by
  subst hr₀
  subst hr₁
  rw [div_le_div_iff hg₀ hg₁]
  nlinarith

end RiemannEssence
