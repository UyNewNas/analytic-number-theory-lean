import Mathlib.Data.Real.Basic

/-!
# RH 塔程序——κ_pred > 3/8 的代数（c₁ = 3/8 条件）

κ_pred(w) = (w−1)/(w+1)。κ_pred > 3/8 ⟺ 8(w−1) > 3(w+1) ⟺ w > 11/5。
（注意：κ_pred(25) = 0.344 < 3/8；c₁ = 3/8 的单点用真 κ = κ_pred(1+ε)，ε(25)=0.0996。）
-/

namespace RiemannEssence

-- κ_pred(w) > 3/8 ⟸ w > 11/5
lemma kappa_pred_gt_three_eighths {w : ℝ} (hw : 11 / 5 < w) :
    3 / 8 < (w - 1) / (w + 1) := by
  have hpos : 0 < w + 1 := by nlinarith [hw]
  rw [lt_div_iff hpos]
  nlinarith [hw]

-- 等价：κ_pred(w) > 3/8 ↔ w > 11/5（w + 1 > 0 时）
lemma kappa_pred_gt_three_eighths_iff {w : ℝ} (hw : 0 < w + 1) :
    3 / 8 < (w - 1) / (w + 1) ↔ 11 / 5 < w := by
  rw [lt_div_iff hw]
  constructor <;> intro h <;> nlinarith

-- κ_pred 在 w > 1 时取值于 (0,1)（单调递增的界）
lemma kappa_pred_bounds {w : ℝ} (hw : 1 < w) :
    0 < (w - 1) / (w + 1) ∧ (w - 1) / (w + 1) < 1 := by
  have hpos : 0 < w + 1 := by linarith
  constructor
  · rw [div_pos_iff]
    constructor <;> linarith
  · rw [div_lt_one hpos]
    nlinarith

end RiemannEssence
