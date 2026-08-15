import Mathlib.Data.Real.Basic

/-!
# RH 塔程序——d_m = κ(m)/m 的单调性代数（56 §2）

d_m = κ(m)/m（68 号精确恒等式）。d 递减的条件：
d_{m+1} < d_m ⟺ κ(m+1)/κ(m) < (m+1)/m = 1 + 1/m（κ 斜率界）。
-/

namespace RiemannEssence

-- d_{m+1} < d_m 的交叉相乘等价
lemma d_decreasing_cross {m κm κm1 : ℝ} (hm : 0 < m) (hκ : 0 < κm) :
    κm1 / (m + 1) < κm / m ↔ m * κm1 < (m + 1) * κm := by
  have hm1 : 0 < m + 1 := by linarith
  constructor <;> intro h <;> nlinarith

-- 比值形式：κ(m+1)/κ(m) < (m+1)/m
lemma d_decreasing_ratio {m κm κm1 : ℝ} (hm : 0 < m) (hκ : 0 < κm) :
    κm1 / (m + 1) < κm / m ↔ κm1 / κm < (m + 1) / m := by
  have hm1 : 0 < m + 1 := by linarith
  constructor <;> intro h
  · -- κm1/(m+1) < κm/m ⟹ κm1/κm < (m+1)/m
    have hcross : m * κm1 < (m + 1) * κm := (d_decreasing_cross (m := m) (κm := κm) (κm1 := κm1) hm hκ).1 h
    exact (div_lt_div_iff hκ hm).2 (by nlinarith)
  · -- 反向
    have hcross : m * κm1 < (m + 1) * κm := (div_lt_div_iff hκ hm).1 h
    exact (d_decreasing_cross (m := m) (κm := κm) (κm1 := κm1) hm hκ).2 (by nlinarith)

end RiemannEssence
