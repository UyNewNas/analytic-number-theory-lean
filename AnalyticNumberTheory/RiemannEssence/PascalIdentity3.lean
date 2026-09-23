import Mathlib.Data.Real.Basic

/-!
# RH 塔程序——Pascal 恒等式 Δ_{4,n} = t²·T_{3,n}（一般 d 模式）

T_{3,n}(t) = J^{3,n+1}(t)² − J^{3,n}(t)J^{3,n+2}(t)
Δ_{4,n}(t) = J^{4,n}(t)² − J^{3,n}(t)J^{5,n}(t)
恒等式：Δ_{4,n}(t) = t²·T_{3,n}(t)（58-top-link 的 (ii)，d=3）。
-/

namespace RiemannEssence

-- Δ_{4,n}(t) = t²·T_{3,n}(t)（g_k = γ(n+k)）
lemma Delta4_eq_t2_T3 (g₀ g₁ g₂ g₃ g₄ g₅ t : ℝ) :
    (g₀ + 4 * g₁ * t + 6 * g₂ * t ^ 2 + 4 * g₃ * t ^ 3 + g₄ * t ^ 4) ^ 2 -
      (g₀ + 3 * g₁ * t + 3 * g₂ * t ^ 2 + g₃ * t ^ 3) *
        (g₀ + 5 * g₁ * t + 10 * g₂ * t ^ 2 + 10 * g₃ * t ^ 3 + 5 * g₄ * t ^ 4 + g₅ * t ^ 5)
      = t ^ 2 * ((g₁ + 3 * g₂ * t + 3 * g₃ * t ^ 2 + g₄ * t ^ 3) ^ 2 -
          (g₀ + 3 * g₁ * t + 3 * g₂ * t ^ 2 + g₃ * t ^ 3) *
            (g₂ + 3 * g₃ * t + 3 * g₄ * t ^ 2 + g₅ * t ^ 3)) := by
  ring

end RiemannEssence
