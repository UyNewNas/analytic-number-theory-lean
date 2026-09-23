import Mathlib.Data.Real.Basic

/-!
# RH 塔程序——κ↑ 的差分代数（claim-e 核，58 §3.7）

κ(m) = κ_pred(m)(1+ε(m))。κ(m+1) > κ(m) ⟺
Δκ_pred(1+ε(m+1)) > κ_pred(m)·(ε(m) − ε(m+1))（Δε 差分控制）。
-/

namespace RiemannEssence

-- κ↑ 的等价代数：Δκp(1+ε₁) > kp·(ε₀−ε₁)
lemma kappa_increasing_iff {kp Δkp ε₀ ε₁ : ℝ} :
    (kp + Δkp) * (1 + ε₁) > kp * (1 + ε₀) ↔
      Δkp * (1 + ε₁) > kp * (ε₀ - ε₁) := by
  constructor <;> intro h <;> nlinarith

-- 非严格版
lemma kappa_mono_iff {kp Δkp ε₀ ε₁ : ℝ} :
    (kp + Δkp) * (1 + ε₁) ≥ kp * (1 + ε₀) ↔
      Δkp * (1 + ε₁) ≥ kp * (ε₀ - ε₁) := by
  constructor <;> intro h <;> nlinarith

-- 充分条件：Δε > 0（ε 递减）且 Δkp(1+ε₁) > kp·Δε
lemma kappa_increasing_sufficient {kp Δkp ε₀ ε₁ : ℝ} (hkp : 0 < kp)
    (hΔε : 0 ≤ ε₀ - ε₁) (hmain : kp * (ε₀ - ε₁) < Δkp * (1 + ε₁)) :
    (kp + Δkp) * (1 + ε₁) > kp * (1 + ε₀) := by
  exact (kappa_increasing_iff (kp := kp) (Δkp := Δkp) (ε₀ := ε₀) (ε₁ := ε₁)).2 hmain

end RiemannEssence
