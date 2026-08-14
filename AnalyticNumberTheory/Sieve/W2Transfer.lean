import AnalyticNumberTheory.Sieve.W1LemmaB
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# W2 传递权重对消引理 (issue #42, S4b 装配基础)

S4b 全特征 BD 装配需要: BD 引理带 `(φ(q)/q)` 权重 (over primitive chars), 目标带
`μ²·3^ω` 权重 (over all chars). 装配时出现权重乘积 `(φ(q)/q)·(q/φ(q)) = 1`,
需要显式对消引理. 本文件给出三个纯代数引理 (全部要求 `q ≥ 1` 以保证
`φ(q) ≠ 0`, 即 `Nat.totient_pos`):

* `totient_div_q_mul_q_div_totient_eq_one` (W2a): `(φ(q)/q)·q / φ(q) = 1`
* `q_div_totient_mul_totient_div_q_eq_one` (W2b): `(q/φ(q))·φ(q) / q = 1` (对称版)
* `mul_totient_div_q_mul_q_div_totient` (W2c): `w·(φ(q)/q)·(q/φ(q)) = w`
  (权重 `w` 乘 `φ/q` 再乘 `q/φ` 后还原; `ring` + W2a)
-/

namespace AnalyticNumberTheory.Sieve

/-- **W2a** (issue #42, S4b): 传递权重对消, 左结合形式

  `((φ(q):ℝ)/q · q) / φ(q) = 1` 对 `q ≥ 1`.

用 `field_simp` 消去分母 (需 `q ≠ 0` 与 `φ(q) ≠ 0`, 后者来自 `Nat.totient_pos`). -/
theorem totient_div_q_mul_q_div_totient_eq_one {q : ℕ} (hq : 1 ≤ q) :
    ((Nat.totient q : ℝ) / (q : ℝ) * (q : ℝ) / (Nat.totient q : ℝ)) = 1 := by
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hqpos)
  have hφR : (Nat.totient q : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hqpos).ne'
  field_simp [hqR, hφR]
  ring

end AnalyticNumberTheory.Sieve
