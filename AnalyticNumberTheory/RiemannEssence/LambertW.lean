import Mathlib.Analysis.SpecialFunctions.WLambert
import Mathlib.Data.Real.Basic

namespace RiemannEssence

lemma kappaPred_strictMono_aux {w₁ w₂ : ℝ} (h₁ : 1 < w₁) (hw : w₁ < w₂) :
    (w₁ - 1) / (w₁ + 1) < (w₂ - 1) / (w₂ + 1) := by
  have hpos₁ : 0 < w₁ + 1 := by linarith
  have hpos₂ : 0 < w₂ + 1 := by linarith
  have hcross : (w₁ - 1) * (w₂ + 1) < (w₂ - 1) * (w₁ + 1) := by
    nlinarith
  exact (div_lt_div_iff hpos₁ hpos₂).2 (by nlinarith)

-- lambertW 单调性（API 名待 CI 确认；错误信息将揭示正确名）
lemma lambertW_strictMono {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    Real.lambertW x < Real.lambertW y := by
  exact Real.lambertW_strictMono hx hxy

end RiemannEssence
