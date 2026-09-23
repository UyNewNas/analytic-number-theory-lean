import Mathlib.Analysis.SpecialFunctions.Log
import Mathlib.Data.Real.Basic

/-!
# RH 塔程序供给线——F(m) 差分恒等式

F(m) = log((2m+3)/(2m+1))（57 §3 的代数简化）：
F(m+1) − F(m) = log((2m+5)(2m+1)/(2m+3)²)。
-/

namespace RiemannEssence

lemma F_difference {m : ℝ} (hm : 0 < 2 * m + 3) :
    Real.log ((2 * (m + 1) + 3) / (2 * (m + 1) + 1)) -
      Real.log ((2 * m + 3) / (2 * m + 1)) =
      Real.log ((2 * m + 5) * (2 * m + 1) / (2 * m + 3) ^ 2) := by
  have hA : 0 < 2 * (m + 1) + 3 := by positivity
  have hB : 0 < 2 * (m + 1) + 1 := by positivity
  have hC : 0 < 2 * m + 3 := hm
  have hD : 0 < 2 * m + 1 := by positivity
  rw [Real.log_div hA hB, Real.log_div hC hD]
  have h₁ : 2 * (m + 1) + 3 = 2 * m + 5 := by ring
  have h₂ : 2 * (m + 1) + 1 = 2 * m + 1 := by ring
  rw [h₁, h₂]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_pow]
  rw [Real.log_div]
  ring_nf

end RiemannEssence
