import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log

/-!
# RH 塔程序——d_m > 0（CNV 的推论）

d_m = log(r_m/r_{m+1})。r 递减（CNV：γ 对数凸 ⟹ r_m = γ(m+1)/γ(m) 递减）⟹
d_m > 0。κ(m) = m·d_m > 0（68 号精确恒等式的推论）。
-/

namespace RiemannEssence

-- r₁ < r₀（r 递减）⟹ log(r₀/r₁) > 0
lemma d_pos_of_ratio_decreasing {r₀ r₁ : ℝ} (hr₁ : 0 < r₁) (hdec : r₁ < r₀) :
    0 < Real.log (r₀ / r₁) := by
  have hrat : 1 < r₀ / r₁ := by
    rw [one_lt_div hr₁]
    exact hdec
  exact Real.log_pos hrat

-- d_m > 0 版本（r_m > r_{m+1}）
lemma d_m_pos {r₀ r₁ : ℝ} (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hdec : r₁ < r₀) :
    0 < Real.log (r₀ / r₁) :=
  d_pos_of_ratio_decreasing hr₁ hdec

-- log(r₀/r₁) = log r₀ − log r₁（正性条件）
lemma log_ratio_eq {r₀ r₁ : ℝ} (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) :
    Real.log (r₀ / r₁) = Real.log r₀ - Real.log r₁ := by
  rw [Real.log_div hr₀ hr₁]

end RiemannEssence
