import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Real.Basic

/-!
# RH 塔程序——W 无负实根（Descartes 推论的核）

多项式系数非负且常数项正 ⟹ 在正实数处取正值。
应用于 W(−s)（全正系数，W_neg_coeffs_pos）⟹ W 在负半轴无实根。
-/

namespace RiemannEssence

-- 系数非负 + 常数项正 ⟹ 正实数处取正值
lemma eval_pos_of_coeff_nonneg_const_pos (p : Polynomial ℝ)
    (hp0 : 0 < p.coeff 0) (hpn : ∀ i, 0 ≤ p.coeff i) {x : ℝ} (hx : 0 < x) :
    0 < p.eval x := by
  -- eval = sum_{i in range} coeff i * x^i ≥ coeff 0 * x^0 = coeff 0 > 0
  rw [Polynomial.eval_eq_sum_range]
  have hx0 : 0 < x ^ 0 := by positivity
  have hmain : p.coeff 0 * x ^ 0 ≤
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i := by
    -- 从总和中拆出 i=0 项（其余 ≥ 0）
    calc
      p.coeff 0 * x ^ 0 = p.coeff 0 * x ^ 0 + ∑ i ∈ Finset.range (p.natDegree + 1)  {0}, p.coeff i * x ^ i - 0 := by ring
      _ ≤ p.coeff 0 * x ^ 0 + ∑ i ∈ Finset.range (p.natDegree + 1)  {0}, p.coeff i * x ^ i := by linarith
      _ = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i := by
        -- 0 在 range 内（natDegree ≥ 0）⟹ 拆分恒等式
        rw [← Finset.sum_sdiff]
        · simp
        · simp
  exact lt_of_lt_of_le (by positivity) hmain

end RiemannEssence
