import Mathlib.Data.Real.Basic

/-!
# κ_pred 单调性——辅助引理（第一批 CI 验证，无 sorry）

f(w) = (w−1)/(w+1) 在 w > 1 上严格递增。这是 RH 塔程序供给线
κ_pred(m) = (W(2m/π)−1)/(W(2m/π)+1) 单调性的初等部分。
-/

namespace RiemannEssence

lemma kappaPred_strictMono_aux {w₁ w₂ : ℝ} (h₁ : 1 < w₁) (hw : w₁ < w₂) :
    (w₁ - 1) / (w₁ + 1) < (w₂ - 1) / (w₂ + 1) := by
  have hpos₁ : 0 < w₁ + 1 := by linarith
  have hpos₂ : 0 < w₂ + 1 := by linarith
  have hcross : (w₁ - 1) * (w₂ + 1) < (w₂ - 1) * (w₁ + 1) := by
    nlinarith
  exact (div_lt_div_iff hpos₁ hpos₂).2 (by nlinarith)

end RiemannEssence
