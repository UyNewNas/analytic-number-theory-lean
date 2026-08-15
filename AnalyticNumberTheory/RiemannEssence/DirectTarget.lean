import Mathlib.Data.Real.Basic

/-!
# RH 塔程序——直接目标 (D) 的代数核（62 号）

ε = (A−B)/κ_pred ≤ C/m（直接目标 ε ≤ 2.489/m，C = 2.489）
⟺ B ≥ mF − κ_pred(1 + C/m)（RHS(D) 的 ln(1+CV²) 版本）。
-/

namespace RiemannEssence

-- ε ≤ C/m ⟺ B ≥ mF − κ_pred(1 + C/m)，其中 ε = (mF − κ_pred − B)/κ_pred
lemma eps_bound_iff {m F kp B C : ℝ} (hkp : 0 < kp) (hm : 0 < m) :
    (m * F - kp - B) / kp ≤ C / m ↔
      B ≥ m * F - kp * (1 + C / m) := by
  have hkm : kp * m ≠ 0 := by positivity
  constructor <;> intro h <;> nlinarith

-- 等价形式：B ≥ mF − κ_pred − C·κ_pred/m
lemma eps_bound_iff' {m F kp B C : ℝ} (hkp : 0 < kp) (hm : 0 < m) :
    (m * F - kp - B) / kp ≤ C / m ↔
      B ≥ m * F - kp - C * kp / m := by
  have hkm : kp * m ≠ 0 := by positivity
  constructor <;> intro h <;> nlinarith

end RiemannEssence
