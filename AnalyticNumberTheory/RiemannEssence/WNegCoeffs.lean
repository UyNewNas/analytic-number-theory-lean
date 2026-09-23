import Mathlib.Data.Real.Basic

/-!
# RH 塔程序——W(−s) 全正系数（58-e2n 机制层）

W(s) = (1−a) − 2(1−ab)s + (3−2b−ab²c)s² − 2b(1−bc)s³ + b²(1−c)s⁴。
对 a,b,c ∈ (0,1)：W(−s) 的系数全正（1−a, 2(1−ab), 3−2b−ab²c, 2b(1−bc), b²(1−c)）
⟹ W 在负半轴无实根（Descartes）。
-/

namespace RiemannEssence

-- W(−s) 系数全正：a,b,c ∈ (0,1)
lemma W_neg_coeffs_pos {a b c : ℝ}
    (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hb1 : b < 1)
    (hc : 0 < c) (hc1 : c < 1) :
    0 < 1 - a ∧ 0 < 2 * (1 - a * b) ∧ 0 < 3 - 2 * b - a * b ^ 2 * c ∧
      0 < 2 * b * (1 - b * c) ∧ 0 < b ^ 2 * (1 - c) := by
  constructor
  · linarith
  constructor
  · nlinarith [ha1, hb1]
  constructor
  · have habc : a * b ^ 2 * c < 1 := by nlinarith [ha1, hb1, hc1]
    nlinarith [hb1, habc]
  constructor
  · have hbc : b * c < 1 := by nlinarith [hb1, hc1]
    nlinarith [hb, hbc]
  · nlinarith [hb, hc1]

-- W(−s) 表达式（变量替换 s ↦ −s 后的全正系数多项式的值）
-- 推论（Descartes，正式化留给后续）：W 无负实根。
lemma W_neg_s_coeffs {a b c : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (hc : 0 < c) (hc1 : c < 1) :
    0 < 1 - a ∧ 0 < 2 * (1 - a * b) ∧ 0 < 3 - 2 * b - a * b ^ 2 * c ∧
      0 < 2 * b * (1 - b * c) ∧ 0 < b ^ 2 * (1 - c) :=
  W_neg_coeffs_pos ha ha1 hb hb1 hc hc1

end RiemannEssence
