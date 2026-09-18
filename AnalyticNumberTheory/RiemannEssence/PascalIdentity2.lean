import Mathlib.Data.Real.Basic

/-!
# RH 塔程序——Pascal 恒等式 Δ_{3,n} = t²·T_{2,n}（一般 d 版）

T_{2,n}(t) = J^{2,n+1}(t)² − J^{2,n}(t)J^{2,n+2}(t)
Δ_{3,n}(t) = J^{3,n}(t)² − J^{2,n}(t)J^{4,n}(t)
恒等式：Δ_{3,n}(t) = t²·T_{2,n}(t)（58-top-link 的 (ii) 一般 d 化）。
-/

namespace RiemannEssence

-- Δ_{3,n}(t) = t²·T_{2,n}(t)（g_k = γ(n+k)）
lemma Delta3_eq_t2_T2 (g₀ g₁ g₂ g₃ g₄ t : ℝ) :
    (g₀ + 3 * g₁ * t + 3 * g₂ * t ^ 2 + g₃ * t ^ 3) ^ 2 -
      (g₀ + 2 * g₁ * t + g₂ * t ^ 2) *
        (g₀ + 4 * g₁ * t + 6 * g₂ * t ^ 2 + 4 * g₃ * t ^ 3 + g₄ * t ^ 4)
      = t ^ 2 * ((g₁ + 2 * g₂ * t + g₃ * t ^ 2) ^ 2 -
          (g₀ + 2 * g₁ * t + g₂ * t ^ 2) * (g₂ + 2 * g₃ * t + g₄ * t ^ 2)) := by
  ring

end RiemannEssence
