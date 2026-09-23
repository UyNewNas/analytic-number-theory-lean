import Mathlib.Data.Real.Basic

/-!
# RH 塔程序——ε ≥ 0 侧代数（[M1-7]，57 §4）

ε = (A−B)/κ_pred ≥ 0 ⟺ B ≤ A ⟺ m·ln(1+CV²) ≤ mF − κ_pred（κ_pred > 0）。
-/

namespace RiemannEssence

-- ε ≥ 0 ⟺ B ≤ A（A = mF − κ_pred）
lemma eps_nonneg_iff {m F kp B : ℝ} (hkp : 0 < kp) :
    0 ≤ (m * F - kp - B) / kp ↔ B ≤ m * F - kp := by
  have hpos : 0 < kp := hkp
  constructor <;> intro h
  · have hnum : 0 ≤ m * F - kp - B := by
      have hd := (div_nonneg_iff (b := kp)).mp h
      rcases hd with ⟨h₁, h₂⟩ | ⟨h₃, h₄⟩
      · exact h₁
      · linarith
    nlinarith
  · rw [div_nonneg_iff]
    left
    constructor <;> nlinarith

-- B = m·ln(1+CV²) 版本（B 的定义代入）
lemma eps_nonneg_log {m F kp CV2 : ℝ} (hkp : 0 < kp) :
    0 ≤ (m * F - kp - m * Real.log (1 + CV2)) / kp ↔
      m * Real.log (1 + CV2) ≤ m * F - kp := by
  exact eps_nonneg_iff (m := m) (F := F) (kp := kp) (B := m * Real.log (1 + CV2)) hkp

end RiemannEssence
