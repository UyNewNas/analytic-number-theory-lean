import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log

/-!
# RH 塔程序——κ(n) = n·d_n 恒等式的有理核（68 号）

γ(m) = 4m!M_m/(2m)! 的阶乘结构给出精确相消：
(m+1)(2m+4) = (m+2)(2m+2)（⟹ d_m = κ(m)/m 与矩无关地成立）。
-/

namespace RiemannEssence

-- 有理核：(m+1)(2m+4) = (m+2)(2m+2)
lemma factorial_cancel {m : ℝ} :
    (m + 1) * (2 * m + 4) = (m + 2) * (2 * m + 2) := by
  ring

-- 商形式：(m+1)(2m+4)/((m+2)(2m+2)) = 1（m ≠ -1, -2）
lemma factorial_cancel_div {m : ℝ} (hm1 : m + 1 ≠ 0) (hm2 : m + 2 ≠ 0) :
    (m + 1) * (2 * m + 4) / ((m + 2) * (2 * m + 2)) = 1 := by
  field_simp [hm1, hm2]
  ring

-- log 版本：log((m+1)(2m+4)) = log((m+2)(2m+2))（正性条件下）
lemma factorial_cancel_log {m : ℝ} (hm1 : 0 < m + 1) (hm2 : 0 < m + 2) :
    Real.log ((m + 1) * (2 * m + 4)) = Real.log ((m + 2) * (2 * m + 2)) := by
  congr 1
  exact factorial_cancel (m := m)

end RiemannEssence
