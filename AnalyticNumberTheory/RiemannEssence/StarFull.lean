import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# RH 塔程序——(★) 全陈述（W(1) > 0 ⟺ 绑定不等式）

W(1) = (2−a)(1−b)² − b²(1−a)(1−c)（W_one_identity），
(★)：绑定不等式 (2−e^{−d_n})(1−e^{−d_{n+1}})² > e^{−2d_{n+1}}(1−e^{−d_n})(1−e^{−d_{n+2}})。
本文件：(★) ⟺ W(1) > 0 + exp 参数在 (0,1)。
-/

namespace RiemannEssence

lemma W_one_identity (a b c : ℝ) :
    (1 - a) - 2 * (1 - a * b) + (3 - 2 * b - a * b ^ 2 * c) -
      2 * b * (1 - b * c) + b ^ 2 * (1 - c)
      = (2 - a) * (1 - b) ^ 2 - b ^ 2 * (1 - a) * (1 - c) := by
  ring

-- (★) ⟺ W(1) > 0
lemma star_iff_W1_pos (a b c : ℝ) :
    (2 - a) * (1 - b) ^ 2 > b ^ 2 * (1 - a) * (1 - c) ↔
      (1 - a) - 2 * (1 - a * b) + (3 - 2 * b - a * b ^ 2 * c) -
        2 * b * (1 - b * c) + b ^ 2 * (1 - c) > 0 := by
  rw [W_one_identity a b c]
  constructor <;> intro h <;> linarith

-- exp 参数在 (0,1)：d > 0 ⟹ e^{−d} ∈ (0,1)
lemma exp_neg_mem_unit {x : ℝ} (hx : 0 < x) :
    0 < Real.exp (-x) ∧ Real.exp (-x) < 1 := by
  constructor
  · exact Real.exp_pos (-x)
  · rw [Real.exp_lt_one_iff]
    linarith

-- (★) 的 e 参数版本（d 为正 ⟹ a,b,c ∈ (0,1)）
lemma star_exp_form {d₀ d₁ d₂ : ℝ} (hd₀ : 0 < d₀) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    let a := Real.exp (-d₀)
    let b := Real.exp (-d₁)
    let c := Real.exp (-d₂)
    (2 - a) * (1 - b) ^ 2 > b ^ 2 * (1 - a) * (1 - c) ↔
      (1 - a) - 2 * (1 - a * b) + (3 - 2 * b - a * b ^ 2 * c) -
        2 * b * (1 - b * c) + b ^ 2 * (1 - c) > 0 := by
  dsimp
  exact star_iff_W1_pos (Real.exp (-d₀)) (Real.exp (-d₁)) (Real.exp (-d₂))

end RiemannEssence
