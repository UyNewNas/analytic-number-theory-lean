import Mathlib.Analysis.SpecialFunctions.WLambert
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace RiemannEssence

lemma kappaPred_strictMono_aux {w₁ w₂ : ℝ} (h₁ : 1 < w₁) (hw : w₁ < w₂) :
    (w₁ - 1) / (w₁ + 1) < (w₂ - 1) / (w₂ + 1) := by
  have hpos₁ : 0 < w₁ + 1 := by linarith
  have hpos₂ : 0 < w₂ + 1 := by linarith
  have hcross : (w₁ - 1) * (w₂ + 1) < (w₂ - 1) * (w₁ + 1) := by
    nlinarith
  exact (div_lt_div_iff hpos₁ hpos₂).2 (by nlinarith)

lemma lambertW_strictMono {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    Real.lambertW x < Real.lambertW y := by
  exact Real.lambertW_strictMono hx hxy

-- 主引理：κ_pred(m) = (W(2m/π)−1)/(W(2m/π)+1) 在 m ≥ 25 严格递增
lemma kappaPred_strictMono {m₁ m₂ : ℝ} (hm₁ : 25 ≤ m₁) (hm : m₁ < m₂) :
    let w₁ := Real.lambertW (2 * m₁ / Real.pi)
    let w₂ := Real.lambertW (2 * m₂ / Real.pi)
    (w₁ - 1) / (w₁ + 1) < (w₂ - 1) / (w₂ + 1) := by
  dsimp
  have harg₁ : 0 < 2 * m₁ / Real.pi := by positivity
  have harg₁₂ : 2 * m₁ / Real.pi < 2 * m₂ / Real.pi := by
    have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith
  have hw12 : Real.lambertW (2 * m₁ / Real.pi) < Real.lambertW (2 * m₂ / Real.pi) :=
    lambertW_strictMono harg₁ harg₁₂
  have hw₁ : 1 < Real.lambertW (2 * m₁ / Real.pi) := by
    -- 2m₁/π ≥ 50/π > 12.5 > 3 > e ⟹ W > 1（W 严格递增 + W(e) = 1）
    have hpi_lt4 : Real.pi < 4 := Real.pi_lt_four
    have he_lt3 : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hbig : Real.exp 1 < 2 * m₁ / Real.pi := by
      -- m₁ ≥ 25 ⟹ 2m₁/π ≥ 50/π > 50/4 = 12.5 > 3 > e
      have hfrac : 12.5 < 2 * m₁ / Real.pi := by
        have hm' : 12.5 ≤ 2 * m₁ / 4 := by nlinarith [hm₁]
        have hden : 2 * m₁ / 4 ≤ 2 * m₁ / Real.pi := by
          -- π < 4 ⟹ 1/4 < 1/π ⟹ 2m₁/4 < 2m₁/π（m₁ > 0）
          have hmpos : 0 < m₁ := by linarith [hm₁]
          exact (div_le_div_right (by nlinarith [hmpos])).2 hpi_lt4
        nlinarith [hm', hden]
      nlinarith [hfrac, he_lt3]
    have hw_e : Real.lambertW (Real.exp 1) < Real.lambertW (2 * m₁ / Real.pi) :=
      lambertW_strictMono (Real.exp_pos 1) hbig
    have hlam_self : Real.lambertW (Real.exp 1) = 1 := by
      -- mathlib: Real.lambertW_self（CI 迭代确认名）
      exact Real.lambertW_self
    rwa [hlam_self] at hw_e
  exact kappaPred_strictMono_aux hw₁ hw12

end RiemannEssence
