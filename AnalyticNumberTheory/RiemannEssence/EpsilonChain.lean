import Mathlib.Data.Real.Basic

/-!
# RH 塔程序——ε 代数链（57 §3）

ε = κ_true/κ_pred − 1 = (A − B)/κ_pred，
A = mF − κ_pred，B = m·ln(1+CV²)。
恒等式：A − B = m·(F − ln(1+CV²)) − κ_pred
⟹ ε = m·(F − ln(1+CV²))/κ_pred − 1。
-/

namespace RiemannEssence

-- ε 的代数展开：A − B = m·(F − ln(1+CV²)) − κ_pred
lemma eps_algebra (m F kp CV2 : ℝ) :
    (m * F - kp - m * Real.log (1 + CV2)) / kp =
      m * (F - Real.log (1 + CV2)) / kp - 1 := by
  field_simp
  ring

-- 完整：ε = (mF − kp − m ln(1+CV²))/kp = m(F − ln(1+CV²))/kp − 1
lemma eps_formula (m F kp CV2 : ℝ) (hkp : kp ≠ 0) :
    (m * F - kp - m * Real.log (1 + CV2)) / kp =
      m * (F - Real.log (1 + CV2)) / kp - 1 := by
  field_simp [hkp]
  ring

end RiemannEssence
