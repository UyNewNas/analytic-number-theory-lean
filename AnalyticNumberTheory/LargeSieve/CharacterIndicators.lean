/-
! # AnalyticNumberTheory.LargeSieve.CharacterIndicators

## 等差指示函数的 Dirichlet 特征展开 (图谱 [C] 块)

对模 `q` 的单位 `n, l`, 等差指示函数 `1_{n ≡ l [MOD q]}` 可用 Dirichlet
特征展开:

  Σ_{χ mod q} χ(n)·conj(χ(l)) = φ(q)·1_{n ≡ l [MOD q]}.

这是 Pan 证明中把"同余计数"转成"特征和的均值"的标准步骤 (Liu 2022 §II;
Halberstam--Richert Ch.10): type I/II 界的 Parseval/正交性装置经此接到等差
计数上. 本模块直接装配 `Multiplicative.lean` 的点式特征正交性
(`charOrthSum`), 并把 `ZMod` 相等翻译成自然数同余
(`ZMod.natCast_eq_natCast_iff`).

主要结果:
  * `charOrthSum_unit` — 单位 `a b : ZMod q` 上的正交和 = `if a = b then φ(q) else 0`;
  * `charIndicator_zmod` — 指示函数形式 (ZMod): `Σ_χ χ(a)·star(χ(b)) = φ(q)·1_{a=b}`;
  * `charIndicator` — 自然数同余形式: `Σ_χ χ(n)·star(χ(l)) = if n ≡ l [MOD q] then φ(q) else 0`;
  * `charIndicator_mul` — `φ(q)·1_{n≡l}` 乘法指示形式;
  * `charIndicator_ap` — 归一化点式展开 `1_{n≡l} = φ(q)⁻¹·Σ_χ χ(n)·star(χ(l))`;
  * `charSum_ap` — 等差求和 → 特征和 (type I/II 的 Parseval 接缝):
    `Σ_{n≤N, n≡l [MOD q]} a_n = φ(q)⁻¹·Σ_χ star(χ(l))·Σ_{n≤N} a_n·χ(n)`.

参考: Liu, "On the weighted Pan theorem" (2022) §II--§III;
Halberstam--Richert, "Sieve Methods" (1974) Ch. 10; Montgomery (1971) Ch. 1.
-/

import AnalyticNumberTheory.LargeSieve.Multiplicative
import Mathlib.Tactic

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators
open Classical

noncomputable section

/-! ## 1. ZMod 单位上的正交和: 指示函数形式 -/

/-- 单位上的特征正交和 = `if a = b then φ(q) else 0` (ZMod 形式).
`charOrthSum` 的三重条件 (单位 ∧ 单位 ∧ 相等) 在 `ha hb` 下退化为 `a = b`. -/
theorem charOrthSum_unit {q : ℕ} (hq : 0 < q) {a b : ZMod q} (ha : IsUnit a) (hb : IsUnit b) :
    (∑ χ : DirichletCharacter ℂ q, χ a * star (χ b)) =
      if a = b then (Nat.totient q : ℂ) else 0 := by
  rw [charOrthSum hq a b]
  by_cases hab : a = b <;> simp [hab, ha, hb]

/-- **指示函数形式 (ZMod)**: 对单位 `a b`,
  `Σ_χ χ(a)·star(χ(b)) = φ(q)·1_{a=b}`. -/
theorem charIndicator_zmod {q : ℕ} (hq : 0 < q) {a b : ZMod q} (ha : IsUnit a) (hb : IsUnit b) :
    (∑ χ : DirichletCharacter ℂ q, χ a * star (χ b)) =
      (Nat.totient q : ℂ) * (if a = b then 1 else 0) := by
  rw [charOrthSum_unit hq ha hb]
  by_cases hab : a = b <;> simp [hab]

/-! ## 2. 自然数同余形式 -/

/-- **等差指示函数的特征展开 (自然数形式)**: 对单位 `n, l`,
  `Σ_χ χ(n)·star(χ(l)) = if n ≡ l [MOD q] then φ(q) else 0`
(`ZMod` 相等 ⟺ 模 `q` 同余, `ZMod.natCast_eq_natCast_iff`). -/
theorem charIndicator {q : ℕ} (hq : 0 < q) {n l : ℕ} (hn : IsUnit (n : ZMod q)) (hl : IsUnit (l : ZMod q)) :
    (∑ χ : DirichletCharacter ℂ q, χ (n : ZMod q) * star (χ (l : ZMod q))) =
      if n ≡ l [MOD q] then (Nat.totient q : ℂ) else 0 := by
  rw [charOrthSum_unit hq (a := (n : ZMod q)) (b := (l : ZMod q)) hn hl]
  by_cases hmod : n ≡ l [MOD q]
  · have heq : (n : ZMod q) = (l : ZMod q) := (ZMod.natCast_eq_natCast_iff n l q).mpr hmod
    simp [heq, hmod]
  · have hne : ¬ (n : ZMod q) = (l : ZMod q) := by
      intro h
      exact hmod ((ZMod.natCast_eq_natCast_iff n l q).mp h)
    simp [hne, hmod]

/-- 指示函数乘法形式: `Σ_χ χ(n)·star(χ(l)) = φ(q)·1_{n≡l}`. -/
theorem charIndicator_mul {q : ℕ} (hq : 0 < q) {n l : ℕ} (hn : IsUnit (n : ZMod q)) (hl : IsUnit (l : ZMod q)) :
    (∑ χ : DirichletCharacter ℂ q, χ (n : ZMod q) * star (χ (l : ZMod q))) =
      (Nat.totient q : ℂ) * (if n ≡ l [MOD q] then 1 else 0) := by
  rw [charIndicator hq hn hl]
  by_cases hmod : n ≡ l [MOD q] <;> simp [hmod]

/-! ## 3. 归一化点式展开与等差求和 -/

/-- **归一化点式展开**: 对单位 `l`, 对任意 `n : ℕ`,
  `1_{n≡l} = φ(q)⁻¹·Σ_χ χ(n)·star(χ(l))`
(当 `n` 非单位时 `χ(n) = 0` 使右边为 0; 当 `n ≡ l` 时 `n` 自动是单位). -/
theorem charIndicator_ap {q : ℕ} (hq : 0 < q) {l : ℕ} (hl : IsUnit (l : ZMod q)) (n : ℕ) :
    (if n ≡ l [MOD q] then (1 : ℂ) else 0) =
      (Nat.totient q : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        χ (n : ZMod q) * star (χ (l : ZMod q)) := by
  by_cases hmod : n ≡ l [MOD q]
  · have hn : IsUnit (n : ZMod q) := by
      have heq : (n : ZMod q) = (l : ZMod q) := (ZMod.natCast_eq_natCast_iff n l q).mpr hmod
      simpa [heq] using hl
    have hφ : (Nat.totient q : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr hq).ne'
    have hsum : ∑ χ : DirichletCharacter ℂ q, χ (n : ZMod q) * star (χ (l : ZMod q)) =
        (Nat.totient q : ℂ) := by
      simpa [hmod] using charIndicator hq hn hl
    rw [if_pos hmod, hsum]
    exact (inv_mul_cancel₀ hφ).symm
  · by_cases hn : IsUnit (n : ZMod q)
    · have hsum : ∑ χ : DirichletCharacter ℂ q, χ (n : ZMod q) * star (χ (l : ZMod q)) = 0 := by
        simpa [hmod] using charIndicator hq hn hl
      rw [if_neg hmod, hsum]
      simp
    · have hsum0 : (∑ χ : DirichletCharacter ℂ q, χ (n : ZMod q) * star (χ (l : ZMod q))) = 0 := by
        apply Finset.sum_eq_zero
        intro χ hχ
        rw [χ.map_nonunit hn, zero_mul]
      rw [if_neg hmod, hsum0]
      simp

/-- **等差求和 → 特征和** (type I/II 的 Parseval 接缝): 对单位 `l`,
  `Σ_{n≤N, n≡l [MOD q]} a_n = φ(q)⁻¹·Σ_χ star(χ(l))·Σ_{n≤N} a_n·χ(n)`. -/
theorem charSum_ap {q : ℕ} (hq : 0 < q) {l : ℕ} (hl : IsUnit (l : ZMod q)) (a : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), a n * if n ≡ l [MOD q] then 1 else 0) =
      (Nat.totient q : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        star (χ (l : ZMod q)) * ∑ n ∈ Finset.range (N + 1), a n * χ (n : ZMod q) := by
  calc
    (∑ n ∈ Finset.range (N + 1), a n * if n ≡ l [MOD q] then 1 else 0)
        = ∑ n ∈ Finset.range (N + 1),
            a n * ((Nat.totient q : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
              χ (n : ZMod q) * star (χ (l : ZMod q))) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [charIndicator_ap hq hl n]
    _ = (Nat.totient q : ℂ)⁻¹ * ∑ n ∈ Finset.range (N + 1),
          a n * ∑ χ : DirichletCharacter ℂ q, χ (n : ZMod q) * star (χ (l : ZMod q)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = (Nat.totient q : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          star (χ (l : ZMod q)) * ∑ n ∈ Finset.range (N + 1), a n * χ (n : ZMod q) := by
      congr 1
      calc
        ∑ n ∈ Finset.range (N + 1),
            a n * ∑ χ : DirichletCharacter ℂ q, χ (n : ZMod q) * star (χ (l : ZMod q))
            = ∑ n ∈ Finset.range (N + 1), ∑ χ : DirichletCharacter ℂ q,
                a n * (χ (n : ZMod q) * star (χ (l : ZMod q))) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.mul_sum]
        _ = ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.range (N + 1),
              a n * (χ (n : ZMod q) * star (χ (l : ZMod q))) := by
          rw [Finset.sum_comm]
        _ = ∑ χ : DirichletCharacter ℂ q,
              star (χ (l : ZMod q)) * ∑ n ∈ Finset.range (N + 1), a n * χ (n : ZMod q) := by
          apply Finset.sum_congr rfl
          intro χ hχ
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          ring

end

end AnalyticNumberTheory.LargeSieve
