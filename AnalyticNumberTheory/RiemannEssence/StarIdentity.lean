import Mathlib.Data.Real.Basic

/-!
# RH 塔程序——(★) ⟺ W(1) > 0 恒等式的代数核

W(s) = (1−a) − 2(1−ab)s + (3−2b−ab²c)s² − 2b(1−bc)s³ + b²(1−c)s⁴
W(1) = (2−a)(1−b)² − b²(1−a)(1−c)（纯代数恒等式，58-e2n 审计 sympy 恒 0）
a = e^{−d_n}, b = e^{−d_{n+1}}, c = e^{−d_{n+2}}。
-/

namespace RiemannEssence

lemma W_one_identity (a b c : ℝ) :
    (1 - a) - 2 * (1 - a * b) + (3 - 2 * b - a * b ^ 2 * c) -
      2 * b * (1 - b * c) + b ^ 2 * (1 - c)
      = (2 - a) * (1 - b) ^ 2 - b ^ 2 * (1 - a) * (1 - c) := by
  ring

-- 带 a,b,c = e^{-d} 参数的版本（e 幂代入留给后续）
lemma W_one_identity_exp {d₀ d₁ d₂ : ℝ} :
    let a := Real.exp (-d₀)
    let b := Real.exp (-d₁)
    let c := Real.exp (-d₂)
    (1 - a) - 2 * (1 - a * b) + (3 - 2 * b - a * b ^ 2 * c) -
      2 * b * (1 - b * c) + b ^ 2 * (1 - c)
      = (2 - a) * (1 - b) ^ 2 - b ^ 2 * (1 - a) * (1 - c) := by
  dsimp
  ring

end RiemannEssence
