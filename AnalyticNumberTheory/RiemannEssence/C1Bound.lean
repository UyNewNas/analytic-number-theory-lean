import Mathlib.Data.Real.Basic

/-!
# RH 塔程序——c₁ = 3/8 的代数（57 §4.1）

d_m = κ(m)/m（68 号）。κ(m) ≥ 3/8 ⟹ d_m ≥ 3/(8m)（c₁ = 3/8 目标形式）。
-/

namespace RiemannEssence

-- κ ≥ 3/8 ⟹ d = κ/m ≥ 3/(8m)
lemma d_lower_bound {m κ : ℝ} (hm : 0 < m) (hκ : 3 / 8 ≤ κ) :
    3 / (8 * m) ≤ κ / m := by
  calc
    3 / (8 * m) = (3 / 8) / m := by ring
    _ ≤ κ / m := div_le_div_right hm hκ

-- 等价形式：8m·d ≥ 3（交叉相乘，m > 0）
lemma d_lower_bound_cross {m κ : ℝ} (hm : 0 < m) (hκ : 3 / 8 ≤ κ) :
    3 ≤ 8 * m * (κ / m) := by
  have hd : 3 / (8 * m) ≤ κ / m := d_lower_bound hm hκ
  nlinarith

end RiemannEssence
