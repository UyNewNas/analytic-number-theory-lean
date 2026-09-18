import Mathlib.Data.Real.Basic

/-!
# RH 塔程序——W(s) 四次式结构（E(2,n) 机制层）

W(s) = (1−a) − 2(1−ab)s + (3−2b−ab²c)s² − 2b(1−bc)s³ + b²(1−c)s⁴
a = e^{−d_n}, b = e^{−d_{n+1}}, c = e^{−d_{n+2}}（∈ (0,1)）。
本文件：W(s) 的系数结构与 W(1) 的等价形式。
-/

namespace RiemannEssence

-- W(s) 的定义
noncomputable def WQuartic (a b c s : ℝ) : ℝ :=
  (1 - a) - 2 * (1 - a * b) * s + (3 - 2 * b - a * b ^ 2 * c) * s ^ 2 -
    2 * b * (1 - b * c) * s ^ 3 + b ^ 2 * (1 - c) * s ^ 4

-- W(1) = (2−a)(1−b)² − b²(1−a)(1−c)
lemma WQuartic_one (a b c : ℝ) :
    WQuartic a b c 1 = (2 - a) * (1 - b) ^ 2 - b ^ 2 * (1 - a) * (1 - c) := by
  unfold WQuartic
  ring

-- (★) 绑定不等式 ⟺ W(1) > 0
lemma star_iff_WQuartic_one_pos (a b c : ℝ) :
    (2 - a) * (1 - b) ^ 2 > b ^ 2 * (1 - a) * (1 - c) ↔
      WQuartic a b c 1 > 0 := by
  rw [WQuartic_one]
  constructor <;> intro h <;> linarith

end RiemannEssence
