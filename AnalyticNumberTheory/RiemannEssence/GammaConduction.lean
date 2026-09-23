import Mathlib.Data.Real.Basic

/-!
# RH 塔程序——γ 传导恒等式（68 号）

γ(n) = κ(n)/n − 2κ(n+1)/(n+1) + κ(n+2)/(n+2)（κ(n)=n·d_n 精确恒等式的推论）。
展开：γ = 2κ(n)/(n(n+1)(n+2)) − Δ₁(n+3)/((n+1)(n+2)) + Δ₂/(n+2)，
Δ₁ = κ(n+1)−κ(n)，Δ₂ = κ(n+2)−κ(n+1)。
-/

namespace RiemannEssence

-- γ 展开恒等式（Δ₁ = k1−k0, Δ₂ = k2−k1）
lemma gamma_expansion {n k0 k1 k2 : ℝ}
    (hn : n ≠ 0) (hn1 : n + 1 ≠ 0) (hn2 : n + 2 ≠ 0) :
    k0 / n - 2 * k1 / (n + 1) + k2 / (n + 2) =
      2 * k0 / (n * (n + 1) * (n + 2)) -
        (k1 - k0) * (n + 3) / ((n + 1) * (n + 2)) + (k2 - k1) / (n + 2) := by
  field_simp [hn, hn1, hn2]
  ring

-- 带 Δ 记法的版本
lemma gamma_expansion_delta {n k0 Δ₁ Δ₂ : ℝ}
    (hn : n ≠ 0) (hn1 : n + 1 ≠ 0) (hn2 : n + 2 ≠ 0) :
    k0 / n - 2 * (k0 + Δ₁) / (n + 1) + (k0 + Δ₁ + Δ₂) / (n + 2) =
      2 * k0 / (n * (n + 1) * (n + 2)) -
        Δ₁ * (n + 3) / ((n + 1) * (n + 2)) + Δ₂ / (n + 2) := by
  field_simp [hn, hn1, hn2]
  ring

-- 线性 Δ 近似：Δ₁ ≈ Δ₂ = Δ ⟹ γ = (2κ − 2nΔ)/(n(n+1)(n+2))·(1+…)
lemma gamma_linear_delta {n k0 Δ : ℝ}
    (hn : n ≠ 0) (hn1 : n + 1 ≠ 0) (hn2 : n + 2 ≠ 0) :
    k0 / n - 2 * (k0 + Δ) / (n + 1) + (k0 + 2 * Δ) / (n + 2) =
      (2 * k0 - 2 * n * Δ) / (n * (n + 1) * (n + 2)) := by
  field_simp [hn, hn1, hn2]
  ring

end RiemannEssence
