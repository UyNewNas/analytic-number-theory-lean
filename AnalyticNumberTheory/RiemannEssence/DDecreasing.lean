import Mathlib.Data.Real.Basic

/-!
# RH 塔程序——κ 斜率界 ⟹ d 递减（供给线的 d↓ 条件）

d_m = κ(m)/m。κ 斜率界 κ(m+1) ≤ κ(m)(1+1/m) ⟹ d_{m+1} ≤ d_m。
-/

namespace RiemannEssence

-- κ 斜率界 ⟹ d 递减（非严格版）
lemma d_decreasing_of_slope {m κm κm1 : ℝ} (hm : 0 < m) (hκ : 0 < κm)
    (hslope : κm1 ≤ κm * (1 + 1 / m)) :
    κm1 / (m + 1) ≤ κm / m := by
  have hcross : m * κm1 ≤ (m + 1) * κm := by
    -- m·κm1 ≤ m·κm(1+1/m) = κm(m+1)
    nlinarith
  have hm1 : 0 < m + 1 := by linarith
  exact (div_le_div_iff hm hm1).2 (by nlinarith)

-- 严格版
lemma d_decreasing_of_slope_strict {m κm κm1 : ℝ} (hm : 0 < m) (hκ : 0 < κm)
    (hslope : κm1 < κm * (1 + 1 / m)) :
    κm1 / (m + 1) < κm / m := by
  have hcross : m * κm1 < (m + 1) * κm := by
    nlinarith
  have hm1 : 0 < m + 1 := by linarith
  exact (div_lt_div_iff hm hm1).2 (by nlinarith)

-- 等价：κ 的 Δκ/κ 界形式（Δκ ≤ κ/m）
lemma d_decreasing_delta {m κm Δκ : ℝ} (hm : 0 < m) (hκ : 0 < κm)
    (hdel : Δκ ≤ κm / m) :
    (κm + Δκ) / (m + 1) ≤ κm / m := by
  have hslope : κm + Δκ ≤ κm * (1 + 1 / m) := by
    nlinarith
  exact d_decreasing_of_slope hm hκ hslope

end RiemannEssence
