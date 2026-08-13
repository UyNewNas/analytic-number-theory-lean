/-
! # AnalyticNumberTheory.LargeSieve.Multiplicative

## 乘法大筛 (Multiplicative large sieve)

Pan 均值定理证明链的第二块分析台阶 (图谱 LS1 → LS2): 从加法大筛
(`LargeSieve/WellSpaced.lean`) 出发, 经 Dirichlet 特征正交性与有限傅里叶
Parseval, 得到对模 `q ≤ Q` 的所有 (复值) Dirichlet 特征的均值定理

  Σ_{q ≤ Q} (q/φ(q)) · Σ_{χ mod q} |Σ_n a_n·χ(n)|² ≤ C(N, 1/Q²) · Σ_n |a_n|².

证明骨架 (Montgomery 的经典路线, 绕开 Gauss 和的数值):

1. **特征正交性**: 对模 `q` 的所有特征,
   `Σ_χ |S(χ)|² = φ(q)·Σ_{(a,q)=1} |Σ_{n≡a (q)} a_n|²`
   (mathlib `DirichletCharacter.sum_char_inv_mul_char_eq`; 这里
   `χ(n) = 0` 当 `(n,q) > 1` 自动处理互素限制).
2. **有限傅里叶 Parseval**: `Σ_{a mod q} |Σ_{n≡a (q)} a_n|² ≤ (1/q)·Σ_{r mod q} |S(r/q)|²`
   (把同余指示函数用加法特征 `e(nr/q)` 展开, 几何级数核 `Σ_a e(a(r−s)/q) = q·1_{r=s}`).
3. **有理点集 well-spaced**: `X_Q = {r/q : 1 ≤ q ≤ Q, 0 ≤ r < q}` 是
   `1/Q²`-well-spaced (分子分母差分的下界 `≥ 1/(q₁q₂)`).
4. **加法大筛**: 对 `X_Q` 应用 `largeSievePrimal_wellSpaced`, 得乘法大筛
   (`largeSieveMultiplicative`), 常数为加法大筛弱常数 `C(N, 1/Q²)`.

注意: 这里的 `Σ_χ` 遍历模 `q` 的**所有**特征 (而非仅原特征), 故无需 Gauss 和
与原特征诱导; 该版本蕴含经典的原特征版本 (原特征是子集). 弱常数 `C(N,δ)`
来自 LS1 (最强 `N + δ⁻¹` 仍是开放依赖).

参考: Montgomery, "Topics in Multiplicative Number Theory" (1971), Ch. 1;
Iwaniec & Kowalski, "Analytic Number Theory" (2004), Ch. 7.
-/

import AnalyticNumberTheory.LargeSieve.WellSpaced
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators
open Classical

noncomputable section

/-! ## 1. ℂ 的单位根与特征值的共轭 -/

/-- ℂ 有足够的 `n` 次单位根 (`n ≠ 0`): `exp(2πi/n)` 本原, 单位根群循环
(mathlib 只对 `Circle`/代数闭包注册了实例, 这里为 `DirichletCharacter`
正交性定理提供 ℂ 版本). -/
theorem complexHasEnoughRootsOfUnity (n : ℕ) (hn : n ≠ 0) :
    HasEnoughRootsOfUnity ℂ n := by
  classical
  haveI : NeZero n := ⟨hn⟩
  refine { prim := ?_, cyc := ?_ }
  · exact ⟨Complex.exp (2 * Real.pi * Complex.I / (n : ℂ)), Complex.isPrimitiveRoot_exp n hn⟩
  · infer_instance

/-- 模长为 1 的复数的共轭等于其逆. -/
theorem conj_eq_inv_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : star z = z⁻¹ := by
  have hsq : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hmul : z * star z = 1 := by
    have h := Complex.mul_conj z
    rw [hsq] at h
    simpa using h
  have hne : z ≠ 0 := by
    intro hz0
    have : ‖z‖ = 0 := by simp [hz0]
    linarith
  calc
    star z = 1 * star z := by rw [one_mul]
    _ = (z⁻¹ * z) * star z := by rw [inv_mul_cancel₀ hne]
    _ = z⁻¹ * (z * star z) := by ring
    _ = z⁻¹ := by rw [hmul, mul_one]

/-- 特征值的共轭等于逆特征值: `conj(χ(a)) = χ⁻¹(a)` (对单位 `a`).
非单位情形在正交性引理中单独处理 (两边均为 0). -/
theorem char_conj_inv {q : ℕ} (χ : DirichletCharacter ℂ q) {a : ZMod q} (ha : IsUnit a) :
    star (χ a) = χ⁻¹ a := by
  have hnorm : ‖χ a‖ = 1 := DirichletCharacter.unit_norm_eq_one χ ha.unit
  have hconj : star (χ a) = (χ a)⁻¹ := conj_eq_inv_of_norm_eq_one hnorm
  have hspec : (↑ha.unit : ZMod q) = a := ha.unit_spec
  have hinv : χ⁻¹ a = (χ a)⁻¹ := by
    rw [MulChar.inv_apply]
    have hrinv : Ring.inverse a = (↑ha.unit⁻¹ : ZMod q) := by
      calc
        Ring.inverse a = Ring.inverse (↑ha.unit : ZMod q) := by rw [hspec]
        _ = (↑ha.unit⁻¹ : ZMod q) := Ring.inverse_unit ha.unit
    rw [hrinv]
    -- χ(↑u⁻¹) = (χ ↑u)⁻¹ = (χ a)⁻¹
    have hmul : χ (↑ha.unit : ZMod q) * χ (↑ha.unit⁻¹ : ZMod q) = 1 := by
      rw [← map_mul χ]
      have hunit : (↑ha.unit : ZMod q) * (↑ha.unit⁻¹ : ZMod q) = 1 := by
        exact Units.val_inv ha.unit
      rw [hunit, χ.map_one]
    have hmu : χ (↑ha.unit⁻¹ : ZMod q) = (χ (↑ha.unit : ZMod q))⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hmul)
    rwa [hspec] at hmu
  rw [hconj]
  exact hinv.symm

/-! ## 2. 模 q 的几何级数核与 Parseval -/

/-- `e(x)` 在整数点取 1: `e(k) = 1` (`k : ℤ`). -/
theorem charReal_int_eq_one (k : ℤ) : charReal (k : ℝ) = 1 := by
  have hf : Int.fract (k : ℝ) = 0 := by
    rw [Int.fract_eq_iff]
    refine ⟨by norm_num, by norm_num, ⟨k, ?_⟩⟩
    simp
  calc
    charReal (k : ℝ) = charReal (Int.fract (k : ℝ)) := charReal_eq_charReal_fract (k : ℝ)
    _ = charReal 0 := by rw [hf]
    _ = 1 := charReal_zero

/-- **几何级数核 (模 q)**: `Σ_{r<q} e(r·k/q) = q·1_{q|k}` 对整数 `k`.
`q | k` 时每项为 1; 否则用几何级数公式 (分子 `e(k) = 1`). -/
theorem geomSum_zmod_charReal {q : ℕ} (hq : 0 < q) (k : ℤ) :
    (∑ r ∈ Finset.range q, charReal ((k : ℝ) * (r : ℝ) / (q : ℝ))) =
      if (q : ℤ) ∣ k then (q : ℂ) else 0 := by
  by_cases hk : (q : ℤ) ∣ k
  · -- q | k: k = q·m, 每项 e(r·m) = 1
    rcases hk with ⟨m, hm⟩
    have hk' : (q : ℤ) ∣ k := ⟨m, hm⟩
    have hsum : (∑ r ∈ Finset.range q, charReal ((k : ℝ) * (r : ℝ) / (q : ℝ))) =
        ∑ r ∈ Finset.range q, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro r hr
      have harg : (k : ℝ) * (r : ℝ) / (q : ℝ) = ((m * r : ℤ) : ℝ) := by
        calc
          (k : ℝ) * (r : ℝ) / (q : ℝ)
              = ((k * (r : ℤ) : ℤ) : ℝ) / (q : ℝ) := by
                norm_num
          _ = (((m * (r : ℤ) : ℤ) * (q : ℤ) : ℤ) : ℝ) / (q : ℝ) := by
                have hint : k * (r : ℤ) = (m * (r : ℤ)) * (q : ℤ) := by
                  rw [hm]
                  ring
                rw [hint]
          _ = ((m * (r : ℤ) : ℤ) : ℝ) := by
                field_simp [hq.ne']
                norm_cast
                ring
          _ = ((m * r : ℤ) : ℝ) := by
                norm_num
      rw [harg, charReal_int_eq_one]
    rw [if_pos hk', hsum]
    simp
  · -- ¬ q | k: 几何级数, 分子 e(k·q/q) = e(k) = 1, 分母 ≠ 0
    have hθ : ¬ ∃ t : ℤ, (t : ℝ) = (k : ℝ) / (q : ℝ) := by
      intro ht
      rcases ht with ⟨t, ht⟩
      apply hk
      refine ⟨t, ?_⟩
      -- (k:ℝ)/(q:ℝ) = t ⟹ k = t·q (作为整数)
      have hkmul : (k : ℝ) = (t : ℝ) * (q : ℝ) := by
        calc
          (k : ℝ) = (k : ℝ) / (q : ℝ) * (q : ℝ) := by field_simp [hq.ne']
          _ = (t : ℝ) * (q : ℝ) := by rw [ht]
      have hint : k = t * (q : ℤ) := by
        exact_mod_cast hkmul
      simpa [mul_comm] using hint
    have hz : charReal ((k : ℝ) / (q : ℝ)) ≠ 1 := by
      exact charReal_ne_one_of_not_int hθ
    have hg := geomSum_exp_eq_geomSeries q hz
    -- Σ_{r<q} e(r·(k/q)) = (e(q·(k/q)) − 1)/(e(k/q) − 1)
    -- 且 e(q·(k/q)) = e(k) = 1, 所以分子为 0
    have hnum : charReal (q * ((k : ℝ) / (q : ℝ))) = 1 := by
      have : q * ((k : ℝ) / (q : ℝ)) = (k : ℝ) := by
        field_simp [hq.ne']
      rw [this, charReal_int_eq_one]
    have hg' : (∑ r ∈ Finset.range q, charReal ((r : ℝ) * ((k : ℝ) / (q : ℝ)))) =
        (charReal (q * ((k : ℝ) / (q : ℝ))) - 1) / (charReal ((k : ℝ) / (q : ℝ)) - 1) :=
      hg
    have hzero : (charReal (q * ((k : ℝ) / (q : ℝ))) - 1) / (charReal ((k : ℝ) / (q : ℝ)) - 1) = 0 := by
      rw [hnum]
      simp
    rw [if_neg hk]
    calc
      (∑ r ∈ Finset.range q, charReal ((k : ℝ) * (r : ℝ) / (q : ℝ)))
          = ∑ r ∈ Finset.range q, charReal ((r : ℝ) * ((k : ℝ) / (q : ℝ))) := by
            apply Finset.sum_congr rfl
            intro r hr
            congr 1
            field_simp [hq.ne']
      _ = 0 := by rw [hg', hzero]

/-- **有限傅里叶 Parseval (模 q)**: 对任意 `z : ℕ → ℂ`,
  `Σ_{a<q} |Σ_{r<q} e(ar/q)·z_r|² = q·Σ_{r<q} |z_r|²`. -/
theorem zmodParseval {q : ℕ} (hq : 0 < q) (z : ℕ → ℂ) :
    (∑ a ∈ Finset.range q, (‖∑ r ∈ Finset.range q,
        charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z r‖ ^ 2 : ℂ)) =
      (q : ℂ) * ∑ r ∈ Finset.range q, (‖z r‖ ^ 2 : ℂ) := by
  calc
    (∑ a ∈ Finset.range q, (‖∑ r ∈ Finset.range q,
        charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z r‖ ^ 2 : ℂ))
        = ∑ a ∈ Finset.range q,
            ∑ r ∈ Finset.range q,
              ∑ s ∈ Finset.range q,
                (charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z r) *
                  star (charReal ((a : ℝ) * (s : ℝ) / (q : ℝ)) * z s) := by
          apply Finset.sum_congr rfl
          intro a ha
          have hcast : (‖∑ r ∈ Finset.range q,
              charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z r‖ ^ 2 : ℂ) =
              (‖∑ r ∈ Finset.range q,
                charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z r‖ : ℂ) ^ 2 := by
            norm_num
          rw [hcast]
          exact normSq_sum_eq_sum_mul_star (Finset.range q)
            (fun r => charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z r)
    _ = ∑ r ∈ Finset.range q,
          ∑ s ∈ Finset.range q,
            z r * star (z s) * (∑ a ∈ Finset.range q,
              charReal ((a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ))) := by
          -- 交换求和顺序, 并把 e(ar/q)·star(e(as/q)) 合并成 e(a(r−s)/q)
          have hcross : ∀ a r s : ℕ,
              charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * star (charReal ((a : ℝ) * (s : ℝ) / (q : ℝ))) =
                charReal ((a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ)) := by
            intro a r s
            have h1 : charReal ((a : ℝ) * (s : ℝ) / (q : ℝ)) =
                charReal (((a : ℝ) * (r : ℝ) / (q : ℝ)) - ((a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ))) := by
              congr 1
              field_simp [hq.ne']
              ring
            -- star(e(x)) = e(−x), 再用 e(x−y) = e(x)·e(−y)
            have hs : star (charReal ((a : ℝ) * (s : ℝ) / (q : ℝ))) =
                charReal (-((a : ℝ) * (s : ℝ) / (q : ℝ))) := (charReal_neg _).symm
            have hsum' : charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) *
                charReal (-((a : ℝ) * (s : ℝ) / (q : ℝ))) =
                charReal ((a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ)) := by
              have harg : (a : ℝ) * (r : ℝ) / (q : ℝ) + -((a : ℝ) * (s : ℝ) / (q : ℝ)) =
                  (a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ) := by
                field_simp [hq.ne']
                ring
              rw [← charReal_add, harg]
            rw [hs]
            exact hsum'
          -- 用 sum_comm 把 Σ_a Σ_r Σ_s 换成 Σ_r Σ_s Σ_a
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro s hs
          -- 先把 RHS 的 z r·star(z s) 提取进和
          rw [Finset.mul_sum]
          -- 逐项化简
          apply Finset.sum_congr rfl
          intro a ha
          have hterm : (charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z r) *
              star (charReal ((a : ℝ) * (s : ℝ) / (q : ℝ)) * z s) =
              z r * star (z s) * charReal ((a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ)) := by
            calc
              (charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) * z r) *
                  star (charReal ((a : ℝ) * (s : ℝ) / (q : ℝ)) * z s)
                  = charReal ((a : ℝ) * (r : ℝ) / (q : ℝ)) *
                      star (charReal ((a : ℝ) * (s : ℝ) / (q : ℝ))) * (z r * star (z s)) := by
                    rw [star_mul]
                    ring
              _ = charReal ((a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ)) * (z r * star (z s)) := by
                    rw [hcross a r s]
              _ = z r * star (z s) * charReal ((a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ)) := by ring
          rw [hterm]
    _ = (q : ℂ) * ∑ r ∈ Finset.range q, (‖z r‖ ^ 2 : ℂ) := by
          -- 内层核: Σ_a e(a(r−s)/q) = q·1_{r=s} (r,s < q)
          have hkern : ∀ r s : ℕ, r ∈ Finset.range q → s ∈ Finset.range q →
              (∑ a ∈ Finset.range q,
                charReal ((a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ))) =
                if r = s then (q : ℂ) else 0 := by
            intro r s hr hs
            by_cases hrs : r = s
            · subst hrs
              rw [if_pos rfl]
              calc
                (∑ a ∈ Finset.range q, charReal ((a : ℝ) * ((r : ℝ) - (r : ℝ)) / (q : ℝ)))
                    = ∑ a ∈ Finset.range q, (1 : ℂ) := by
                      apply Finset.sum_congr rfl
                      intro a ha
                      have h0 : (a : ℝ) * ((r : ℝ) - (r : ℝ)) / (q : ℝ) = 0 := by ring
                      rw [h0, charReal_zero]
                _ = (q : ℂ) := by simp
            · rw [if_neg hrs]
              have hdiv : ¬ (q : ℤ) ∣ ((r : ℤ) - (s : ℤ)) := by
                intro hd
                rcases hd with ⟨m, hm⟩
                have hne : (r : ℤ) ≠ (s : ℤ) := by exact_mod_cast hrs
                have hz : (r : ℤ) - (s : ℤ) ≠ 0 := sub_ne_zero.mpr hne
                have hm0 : m ≠ 0 := by
                  intro hm0
                  rw [hm0, mul_zero] at hm
                  exact hz hm
                have hqle : (q : ℤ) ≤ ((r : ℤ) - (s : ℤ)).natAbs := by
                  have hqm : (r : ℤ) - (s : ℤ) = (q : ℤ) * m := hm
                  have habs : ((r : ℤ) - (s : ℤ)).natAbs = (q : ℤ) * |m| := by
                    rw [hqm, Int.natAbs_mul, Int.natAbs_natCast, Int.abs_eq_natAbs]
                    norm_num
                  have hm1 : 1 ≤ |m| := Int.one_le_abs hm0
                  have hq0 : 0 ≤ (q : ℤ) := by exact_mod_cast (Nat.zero_le q)
                  rw [habs]
                  nlinarith
                have hlt : ((r : ℤ) - (s : ℤ)).natAbs < (q : ℤ) := by
                  have h1 : (r : ℤ) - (s : ℤ) < (q : ℤ) := by
                    have hrq : (r : ℤ) < (q : ℤ) := by exact_mod_cast (Finset.mem_range.mp hr)
                    have hs0 : 0 ≤ (s : ℤ) := by exact_mod_cast (Nat.zero_le s)
                    linarith
                  have h2 : -(q : ℤ) < (r : ℤ) - (s : ℤ) := by
                    have hsq : (s : ℤ) < (q : ℤ) := by exact_mod_cast (Finset.mem_range.mp hs)
                    have hr0 : 0 ≤ (r : ℤ) := by exact_mod_cast (Nat.zero_le r)
                    linarith
                  have hlt' : |(r : ℤ) - (s : ℤ)| < (q : ℤ) := (abs_lt).2 ⟨h2, h1⟩
                  rwa [Int.abs_eq_natAbs] at hlt'
                linarith
              have hgeo' : (∑ a ∈ Finset.range q,
                  charReal ((↑((r : ℤ) - (s : ℤ)) : ℝ) * (a : ℝ) / (q : ℝ))) = 0 := by
                have hgeo := geomSum_zmod_charReal hq ((r : ℤ) - (s : ℤ))
                rw [hgeo, if_neg hdiv]
              calc
                (∑ a ∈ Finset.range q, charReal ((a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ)))
                    = ∑ a ∈ Finset.range q,
                        charReal ((↑((r : ℤ) - (s : ℤ)) : ℝ) * (a : ℝ) / (q : ℝ)) := by
                      apply Finset.sum_congr rfl
                      intro a ha
                      congr 1
                      have hc : (↑((r : ℤ) - (s : ℤ)) : ℝ) = (r : ℝ) - (s : ℝ) := by
                        norm_num
                      rw [hc]
                      ring
                _ = 0 := hgeo'
          calc
            (∑ r ∈ Finset.range q, ∑ s ∈ Finset.range q,
                z r * star (z s) * (∑ a ∈ Finset.range q,
                  charReal ((a : ℝ) * ((r : ℝ) - (s : ℝ)) / (q : ℝ))))
                = ∑ r ∈ Finset.range q, ∑ s ∈ Finset.range q,
                    z r * star (z s) * (if r = s then (q : ℂ) else 0) := by
                  apply Finset.sum_congr rfl
                  intro r hr
                  apply Finset.sum_congr rfl
                  intro s hs
                  rw [hkern r s hr hs]
            _ = ∑ r ∈ Finset.range q, z r * star (z r) * (q : ℂ) := by
                  apply Finset.sum_congr rfl
                  intro r hr
                  calc
                    (∑ s ∈ Finset.range q, z r * star (z s) * if r = s then (q : ℂ) else 0)
                        = z r * star (z r) * if r = r then (q : ℂ) else 0 := by
                          refine Finset.sum_eq_single r ?_ ?_
                          · intro b hb hbr
                            simp [hbr.symm]
                          · intro hnr
                            exact False.elim (hnr hr)
                    _ = z r * star (z r) * (q : ℂ) := by simp
            _ = (q : ℂ) * ∑ r ∈ Finset.range q, (‖z r‖ ^ 2 : ℂ) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro r hr
                  have hmul : z r * star (z r) = (‖z r‖ ^ 2 : ℂ) := by
                    have h := Complex.mul_conj (z r)
                    rw [Complex.normSq_eq_norm_sq] at h
                    simpa using h
                  rw [hmul, mul_comm]

/-! ## 3. 特征正交性 -/

/-- 特征正交性 (点式): 对 `m, n : ZMod q`,
  `Σ_χ χ(m)·conj(χ(n)) = φ(q)·1_{m 单位 ∧ n 单位 ∧ m = n}`. -/
theorem charOrthSum {q : ℕ} (hq : 0 < q) (m n : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, χ m * star (χ n)) =
      if IsUnit m ∧ IsUnit n ∧ m = n then (q.totient : ℂ) else 0 := by
  classical
  haveI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ) :=
    complexHasEnoughRootsOfUnity (Monoid.exponent (ZMod q)ˣ) (by
      -- 有限单位群 (ZMod q)ˣ 的指数非零: 由循环性 (q ≥ 1) 或 card 有限
      have hfin : Finite (ZMod q)ˣ := inferInstance
      exact Monoid.exponent_ne_zero.mpr (Monoid.ExponentExists.of_finite (G := (ZMod q)ˣ)))
  by_cases hm : IsUnit m
  · by_cases hn : IsUnit n
    · -- 都单位: χ(m)·conj(χ(n)) = χ(n⁻¹)·χ(m), 用 sum_char_inv_mul_char_eq
      have hsum := DirichletCharacter.sum_char_inv_mul_char_eq ℂ (a := n) hn m
      -- hsum : ∑ χ, χ n⁻¹ * χ m = if n = m then q.totient else 0
      have hrewrite : ∀ χ : DirichletCharacter ℂ q, χ m * star (χ n) = χ n⁻¹ * χ m := by
        intro χ
        have hconj := char_conj_inv χ hn
        -- star(χ n) = χ⁻¹ n = χ(n⁻¹)
        have hinv : χ⁻¹ n = χ (n⁻¹) := by
          rw [MulChar.inv_apply]
          have hspec : (↑hn.unit : ZMod q) = n := hn.unit_spec
          have hrinv : Ring.inverse n = (↑hn.unit⁻¹ : ZMod q) := by
            calc
              Ring.inverse n = Ring.inverse (↑hn.unit : ZMod q) := by rw [hspec]
              _ = (↑hn.unit⁻¹ : ZMod q) := Ring.inverse_unit hn.unit
          rw [hrinv]
          -- 单位逆一致: ↑hn.unit⁻¹ = n⁻¹（n·n⁻¹ = 1 与 n·↑u⁻¹ = 1, 逆唯一）
          have hnval : n.val.Coprime q := by
            have hunit : IsUnit (↑n.val : ZMod q) := by
              simpa [ZMod.natCast_zmod_val] using hn
            exact (ZMod.isUnit_iff_coprime n.val q).mp hunit
          have hmul : n * n⁻¹ = 1 := by
            have h := ZMod.coe_mul_inv_eq_one n.val hnval
            simpa [ZMod.natCast_zmod_val] using h
          have hmul' : n * (↑hn.unit⁻¹ : ZMod q) = 1 := by
            simpa [hspec] using Units.val_inv hn.unit
          have hninv : (↑hn.unit⁻¹ : ZMod q) = n⁻¹ := (inv_unique hmul hmul').symm
          rw [hninv]
        rw [hconj, hinv]
        -- χ m·χ(n⁻¹) = χ(n⁻¹)·χ m（交换）
        rw [mul_comm]
      -- 逐项替换
      have hsum' : (∑ χ : DirichletCharacter ℂ q, χ m * star (χ n)) =
          ∑ χ : DirichletCharacter ℂ q, χ n⁻¹ * χ m := by
        apply Finset.sum_congr rfl
        intro χ hχ
        exact hrewrite χ
      rw [hsum']
      -- 现在和 = if n = m then q.totient else 0（hsum）
      by_cases hmn : m = n
      · have hcond : IsUnit m ∧ IsUnit n ∧ m = n := ⟨hm, hn, hmn⟩
        rw [if_pos hcond]
        rw [hsum, if_pos hmn.symm]
      · have hnot : ¬ (IsUnit m ∧ IsUnit n ∧ m = n) := by
          intro h
          exact hmn h.2.2
        rw [if_neg hnot]
        rw [hsum, if_neg (fun hnm => hmn hnm.symm)]
    · -- n 非单位: star(χ n) = star 0 = 0
      have hχn : ∀ χ : DirichletCharacter ℂ q, star (χ n) = 0 := by
        intro χ
        have hz : χ n = 0 := χ.map_nonunit hn
        simp [hz]
      have hnot : ¬ (IsUnit m ∧ IsUnit n ∧ m = n) := by
        intro h
        exact hn h.2.1
      rw [if_neg hnot]
      -- 和 = 0
      apply Finset.sum_eq_zero
      intro χ hχ
      rw [hχn χ, mul_zero]
  · -- m 非单位: χ(m) = 0
    have hχm : ∀ χ : DirichletCharacter ℂ q, χ m = 0 := by
      intro χ
      exact χ.map_nonunit hm
    have hnot : ¬ (IsUnit m ∧ IsUnit n ∧ m = n) := by
      intro h
      exact hm h.1
    rw [if_neg hnot]
    apply Finset.sum_eq_zero
    intro χ hχ
    rw [hχm χ, zero_mul]

/-- **按剩余类分组**: 对任意 `a`,
  `Σ_{m ∈ Icc} [m 单位]·a_m·star(Σ_{n≡m} a_n) = Σ_{x mod q} [x 单位]·|Σ_{n≡x} a_n|²`. -/
theorem unitClassSum {q : ℕ} [NeZero q] (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    (∑ m ∈ Finset.Icc (M + 1) (M + N),
        (if IsUnit (m : ZMod q) then 1 else 0) * a m *
          star (∑ n ∈ Finset.Icc (M + 1) (M + N),
            a n * if (n : ZMod q) = (m : ZMod q) then 1 else 0))
      = ∑ x : ZMod q, (if IsUnit x then 1 else 0) *
          (‖∑ n ∈ Finset.Icc (M + 1) (M + N),
            a n * if (n : ZMod q) = x then 1 else 0‖ : ℂ) ^ 2 := by
  let S : ZMod q → ℂ := fun x =>
    ∑ n ∈ Finset.Icc (M + 1) (M + N), a n * if (n : ZMod q) = x then 1 else 0
  have hS : ∀ x : ZMod q, S x =
      ∑ n ∈ Finset.Icc (M + 1) (M + N), a n * if (n : ZMod q) = x then 1 else 0 := by
    intro x
    rfl
  calc
    (∑ m ∈ Finset.Icc (M + 1) (M + N),
        (if IsUnit (m : ZMod q) then 1 else 0) * a m * star (S (m : ZMod q)))
        = ∑ x : ZMod q, ∑ m ∈ (Finset.Icc (M + 1) (M + N)).filter (fun m : ℤ => (m : ZMod q) = x),
            (if IsUnit x then 1 else 0) * a m * star (S x) := by
          rw [← Finset.sum_fiberwise (s := Finset.Icc (M + 1) (M + N))
            (g := fun m : ℤ => (m : ZMod q))
            (f := fun m => (if IsUnit (m : ZMod q) then 1 else 0) * a m * star (S (m : ZMod q)))]
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro m hm
          have hclass : (m : ZMod q) = x := (Finset.mem_filter.mp hm).2
          have hunit : (if IsUnit (m : ZMod q) then 1 else 0) =
              (if IsUnit x then 1 else 0) := by
            rw [hclass]
          rw [hclass]
    _ = ∑ x : ZMod q, (if IsUnit x then 1 else 0) *
          (∑ m ∈ (Finset.Icc (M + 1) (M + N)).filter (fun m : ℤ => (m : ZMod q) = x), a m) * star (S x) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = ∑ x : ZMod q, (if IsUnit x then 1 else 0) * (‖S x‖ : ℂ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          -- (Σ_{m≡x} a m)·star(S x) = S x·star(S x) = |S x|²
          have hSx : S x = ∑ m ∈ (Finset.Icc (M + 1) (M + N)).filter (fun m : ℤ => (m : ZMod q) = x), a m := by
            rw [hS]
            calc
              (∑ n ∈ Finset.Icc (M + 1) (M + N), a n * if (n : ZMod q) = x then 1 else 0)
                  = ∑ n ∈ Finset.Icc (M + 1) (M + N), if (n : ZMod q) = x then a n else 0 := by
                    apply Finset.sum_congr rfl
                    intro n hn
                    by_cases h : (n : ZMod q) = x
                    · simp [h]
                    · simp [h]
              _ = ∑ n ∈ (Finset.Icc (M + 1) (M + N)).filter (fun n : ℤ => (n : ZMod q) = x), a n := by
                    rw [← Finset.sum_filter]
          have hnorm : S x * star (S x) = (‖S x‖ : ℂ) ^ 2 := by
            have h := Complex.mul_conj (S x)
            rw [Complex.normSq_eq_norm_sq] at h
            simpa using h
          have hmain : (∑ m ∈ (Finset.Icc (M + 1) (M + N)).filter (fun m : ℤ => (m : ZMod q) = x), a m) *
              star (S x) = (‖S x‖ : ℂ) ^ 2 := by
            rw [← hSx, hnorm]
          calc
            (if IsUnit x then 1 else 0) * (∑ m ∈ (Finset.Icc (M + 1) (M + N)).filter (fun m : ℤ => (m : ZMod q) = x), a m) * star (S x)
                = (if IsUnit x then 1 else 0) * ((∑ m ∈ (Finset.Icc (M + 1) (M + N)).filter (fun m : ℤ => (m : ZMod q) = x), a m) * star (S x)) := by
                  ring
            _ = (if IsUnit x then 1 else 0) * (‖S x‖ : ℂ) ^ 2 := by rw [hmain]
    _ = ∑ x : ZMod q, (if IsUnit x then 1 else 0) *
          (‖∑ n ∈ Finset.Icc (M + 1) (M + N),
            a n * if (n : ZMod q) = x then 1 else 0‖ : ℂ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [← hS]

/-- **内层归约**: `Σ_m Σ_n a_m·star(a_n)·φ(q)·[unit m][unit n][m≡n]`
  `= φ(q)·Σ_m [unit m]·a_m·star(Σ_{n≡m} a_n)`. -/
theorem charInnerReduce {q : ℕ} [NeZero q] (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    (∑ m ∈ Finset.Icc (M + 1) (M + N), ∑ n ∈ Finset.Icc (M + 1) (M + N),
        a m * star (a n) * (q.totient : ℂ) *
          (if IsUnit (m : ZMod q) then 1 else 0) *
          (if IsUnit (n : ZMod q) then 1 else 0) *
          (if (m : ZMod q) = (n : ZMod q) then 1 else 0))
      = (q.totient : ℂ) *
          ∑ m ∈ Finset.Icc (M + 1) (M + N),
            (if IsUnit (m : ZMod q) then 1 else 0) * a m *
              star (∑ n ∈ Finset.Icc (M + 1) (M + N),
                a n * if (n : ZMod q) = (m : ZMod q) then 1 else 0) := by
  have hinner : ∀ m : ℤ,
      (if IsUnit (m : ZMod q) then 1 else 0) *
        (∑ n ∈ Finset.Icc (M + 1) (M + N),
          (if IsUnit (n : ZMod q) then 1 else 0) *
            (if (m : ZMod q) = (n : ZMod q) then 1 else 0) * star (a n)) =
      (if IsUnit (m : ZMod q) then 1 else 0) *
        star (∑ n ∈ Finset.Icc (M + 1) (M + N),
          a n * if (n : ZMod q) = (m : ZMod q) then 1 else 0) := by
    intro m
    by_cases hm : IsUnit (m : ZMod q)
    · have hmain : (∑ n ∈ Finset.Icc (M + 1) (M + N),
            (if IsUnit (n : ZMod q) then 1 else 0) *
              (if (m : ZMod q) = (n : ZMod q) then 1 else 0) * star (a n)) =
          star (∑ n ∈ Finset.Icc (M + 1) (M + N),
            a n * if (n : ZMod q) = (m : ZMod q) then 1 else 0) := by
        calc
          (∑ n ∈ Finset.Icc (M + 1) (M + N),
              (if IsUnit (n : ZMod q) then 1 else 0) *
                (if (m : ZMod q) = (n : ZMod q) then 1 else 0) * star (a n))
              = ∑ n ∈ Finset.Icc (M + 1) (M + N),
                  (if (m : ZMod q) = (n : ZMod q) then 1 else 0) * star (a n) := by
                apply Finset.sum_congr rfl
                intro n hn
                by_cases h : (m : ZMod q) = (n : ZMod q)
                · have hn' : IsUnit (n : ZMod q) := by
                    rw [← h]
                    exact hm
                  simp [h, hn']
                · simp [h]
          _ = star (∑ n ∈ Finset.Icc (M + 1) (M + N),
                  a n * if (n : ZMod q) = (m : ZMod q) then 1 else 0) := by
                have hstep : (∑ n ∈ Finset.Icc (M + 1) (M + N),
                    (if (m : ZMod q) = (n : ZMod q) then 1 else 0) * star (a n)) =
                    ∑ n ∈ Finset.Icc (M + 1) (M + N),
                      star (a n * if (n : ZMod q) = (m : ZMod q) then 1 else 0) := by
                  apply Finset.sum_congr rfl
                  intro n hn
                  by_cases h : (n : ZMod q) = (m : ZMod q)
                  · have h' : (m : ZMod q) = (n : ZMod q) := h.symm
                    rw [if_pos h', if_pos h]
                    simp
                  · have h' : ¬(m : ZMod q) = (n : ZMod q) := fun hmn => h hmn.symm
                    rw [if_neg h', if_neg h]
                    simp
                rw [hstep]
                change (∑ n ∈ Finset.Icc (M + 1) (M + N),
                    (starRingEnd ℂ) (a n * if (n : ZMod q) = (m : ZMod q) then 1 else 0)) =
                  (starRingEnd ℂ) (∑ n ∈ Finset.Icc (M + 1) (M + N),
                    a n * if (n : ZMod q) = (m : ZMod q) then 1 else 0)
                rw [← map_sum (starRingEnd ℂ) (fun n : ℤ =>
                  a n * if (n : ZMod q) = (m : ZMod q) then 1 else 0)
                  (Finset.Icc (M + 1) (M + N))]
      simpa [hm] using hmain
    · simp [hm]
  have hinnerEq : ∀ m : ℤ,
      (∑ n ∈ Finset.Icc (M + 1) (M + N),
          a m * star (a n) * (q.totient : ℂ) *
            (if IsUnit (m : ZMod q) then 1 else 0) *
            (if IsUnit (n : ZMod q) then 1 else 0) *
            (if (m : ZMod q) = (n : ZMod q) then 1 else 0)) =
        (q.totient : ℂ) * (if IsUnit (m : ZMod q) then 1 else 0) * a m *
          (∑ n ∈ Finset.Icc (M + 1) (M + N),
            (if IsUnit (n : ZMod q) then 1 else 0) *
              (if (m : ZMod q) = (n : ZMod q) then 1 else 0) * star (a n)) := by
    intro m
    by_cases hm : IsUnit (m : ZMod q)
    · have h1 : (∑ n ∈ Finset.Icc (M + 1) (M + N),
            a m * star (a n) * (q.totient : ℂ) *
              (if IsUnit (n : ZMod q) then 1 else 0) *
              (if (m : ZMod q) = (n : ZMod q) then 1 else 0)) =
          (q.totient : ℂ) * a m *
            (∑ n ∈ Finset.Icc (M + 1) (M + N),
              (if IsUnit (n : ZMod q) then 1 else 0) *
                (if (m : ZMod q) = (n : ZMod q) then 1 else 0) * star (a n)) := by
        calc
          (∑ n ∈ Finset.Icc (M + 1) (M + N),
              a m * star (a n) * (q.totient : ℂ) *
                (if IsUnit (n : ZMod q) then 1 else 0) *
                (if (m : ZMod q) = (n : ZMod q) then 1 else 0))
              = ∑ n ∈ Finset.Icc (M + 1) (M + N),
                  (q.totient : ℂ) * a m *
                    ((if IsUnit (n : ZMod q) then 1 else 0) *
                      (if (m : ZMod q) = (n : ZMod q) then 1 else 0) * star (a n)) := by
                apply Finset.sum_congr rfl
                intro n hn
                ring
          _ = (q.totient : ℂ) * a m *
                (∑ n ∈ Finset.Icc (M + 1) (M + N),
                  (if IsUnit (n : ZMod q) then 1 else 0) *
                    (if (m : ZMod q) = (n : ZMod q) then 1 else 0) * star (a n)) := by
                rw [← Finset.mul_sum]
      simpa [hm] using h1
    · have hz : (∑ n ∈ Finset.Icc (M + 1) (M + N),
            a m * star (a n) * (q.totient : ℂ) *
              (if IsUnit (m : ZMod q) then 1 else 0) *
              (if IsUnit (n : ZMod q) then 1 else 0) *
              (if (m : ZMod q) = (n : ZMod q) then 1 else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        simp [hm]
      rw [hz]
      simp [hm]
  calc
    (∑ m ∈ Finset.Icc (M + 1) (M + N), ∑ n ∈ Finset.Icc (M + 1) (M + N),
        a m * star (a n) * (q.totient : ℂ) *
          (if IsUnit (m : ZMod q) then 1 else 0) *
          (if IsUnit (n : ZMod q) then 1 else 0) *
          (if (m : ZMod q) = (n : ZMod q) then 1 else 0))
        = (q.totient : ℂ) * ∑ m ∈ Finset.Icc (M + 1) (M + N),
            (if IsUnit (m : ZMod q) then 1 else 0) * a m *
              (∑ n ∈ Finset.Icc (M + 1) (M + N),
                (if IsUnit (n : ZMod q) then 1 else 0) *
                  (if (m : ZMod q) = (n : ZMod q) then 1 else 0) * star (a n)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          simpa [mul_assoc] using hinnerEq m
    _ = (q.totient : ℂ) * ∑ m ∈ Finset.Icc (M + 1) (M + N),
            (if IsUnit (m : ZMod q) then 1 else 0) * a m *
              star (∑ n ∈ Finset.Icc (M + 1) (M + N),
                a n * if (n : ZMod q) = (m : ZMod q) then 1 else 0) := by
          apply congrArg (fun t : ℂ => (q.totient : ℂ) * t) ?_
          apply Finset.sum_congr rfl
          intro m hm
          have h := hinner m
          calc
            (if IsUnit (m : ZMod q) then 1 else 0) * a m *
                (∑ n ∈ Finset.Icc (M + 1) (M + N),
                  (if IsUnit (n : ZMod q) then 1 else 0) *
                    (if (m : ZMod q) = (n : ZMod q) then 1 else 0) * star (a n))
                = a m * ((if IsUnit (m : ZMod q) then 1 else 0) *
                    (∑ n ∈ Finset.Icc (M + 1) (M + N),
                      (if IsUnit (n : ZMod q) then 1 else 0) *
                        (if (m : ZMod q) = (n : ZMod q) then 1 else 0) * star (a n))) := by ring
            _ = a m * ((if IsUnit (m : ZMod q) then 1 else 0) *
                  star (∑ n ∈ Finset.Icc (M + 1) (M + N),
                    a n * if (n : ZMod q) = (m : ZMod q) then 1 else 0)) := by rw [h]
            _ = (if IsUnit (m : ZMod q) then 1 else 0) * a m *
                  star (∑ n ∈ Finset.Icc (M + 1) (M + N),
                    a n * if (n : ZMod q) = (m : ZMod q) then 1 else 0) := by ring

/-- **特征正交性 (不等式)**: 对任意 `a`,
  `Σ_χ |Σ_{n∈Icc} a_n·χ(n)|² ≤ φ(q)·Σ_{x mod q} |Σ_{n≡x} a_n|²` (ℝ 值). -/
theorem charOrthogonality_le {q : ℕ} [NeZero q] (a : ℤ → ℂ) (M : ℤ) (N : ℕ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * χ (n : ZMod q)‖ ^ 2)
      ≤ (q.totient : ℝ) * ∑ x : ZMod q,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * if (n : ZMod q) = x then 1 else 0‖ ^ 2 := by
  let S : DirichletCharacter ℂ q → ℂ := fun χ =>
    ∑ n ∈ Finset.Icc (M + 1) (M + N), a n * χ (n : ZMod q)
  let T : ZMod q → ℂ := fun x =>
    ∑ n ∈ Finset.Icc (M + 1) (M + N), a n * if (n : ZMod q) = x then 1 else 0
  -- 展开 LHS (ℂ 值)
  have hExp : (∑ χ : DirichletCharacter ℂ q, (‖S χ‖ : ℂ) ^ 2) =
      ∑ χ : DirichletCharacter ℂ q,
        ∑ m ∈ Finset.Icc (M + 1) (M + N), ∑ n ∈ Finset.Icc (M + 1) (M + N),
          (a m * χ (m : ZMod q)) * star (a n * χ (n : ZMod q)) := by
    apply Finset.sum_congr rfl
    intro χ hχ
    have hcast : (‖S χ‖ : ℂ) ^ 2 = (‖S χ‖ ^ 2 : ℂ) := by
      dsimp [S]
    rw [hcast]
    exact normSq_sum_eq_sum_mul_star (Finset.Icc (M + 1) (M + N))
      (fun n => a n * χ (n : ZMod q))
  -- 交换求和顺序
  have hSwap : (∑ χ : DirichletCharacter ℂ q,
        ∑ m ∈ Finset.Icc (M + 1) (M + N), ∑ n ∈ Finset.Icc (M + 1) (M + N),
          (a m * χ (m : ZMod q)) * star (a n * χ (n : ZMod q))) =
      ∑ m ∈ Finset.Icc (M + 1) (M + N), ∑ n ∈ Finset.Icc (M + 1) (M + N),
        a m * star (a n) * (∑ χ : DirichletCharacter ℂ q,
          χ (m : ZMod q) * star (χ (n : ZMod q))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    have hst : star (a n * χ (n : ZMod q)) = star (χ (n : ZMod q)) * star (a n) := by
      exact star_mul (a n) (χ (n : ZMod q))
    rw [hst]
    ring
  -- 代入 charOrthSum
  have hSum : (∑ m ∈ Finset.Icc (M + 1) (M + N), ∑ n ∈ Finset.Icc (M + 1) (M + N),
        a m * star (a n) * (∑ χ : DirichletCharacter ℂ q,
          χ (m : ZMod q) * star (χ (n : ZMod q)))) =
      ∑ m ∈ Finset.Icc (M + 1) (M + N), ∑ n ∈ Finset.Icc (M + 1) (M + N),
        a m * star (a n) * (q.totient : ℂ) *
          (if IsUnit (m : ZMod q) then 1 else 0) *
          (if IsUnit (n : ZMod q) then 1 else 0) *
          (if (m : ZMod q) = (n : ZMod q) then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    have hc := charOrthSum (Nat.pos_of_ne_zero (NeZero.ne q)) (m : ZMod q) (n : ZMod q)
    have hsplit : (if IsUnit (m : ZMod q) ∧ IsUnit (n : ZMod q) ∧ (m : ZMod q) = (n : ZMod q)
          then (q.totient : ℂ) else 0) =
        (q.totient : ℂ) * (if IsUnit (m : ZMod q) then 1 else 0) *
          (if IsUnit (n : ZMod q) then 1 else 0) *
          (if (m : ZMod q) = (n : ZMod q) then 1 else 0) := by
      by_cases h1 : IsUnit (m : ZMod q)
      · by_cases h2 : IsUnit (n : ZMod q)
        · by_cases h3 : (m : ZMod q) = (n : ZMod q)
          · simp [h1, h2, h3]
          · simp [h1, h2, h3]
        · simp [h1, h2]
      · simp [h1]
    rw [hc]
    by_cases h1 : IsUnit (m : ZMod q)
    · by_cases h2 : IsUnit (n : ZMod q)
      · by_cases h3 : (m : ZMod q) = (n : ZMod q)
        · simp [h1, h2, h3]
        · simp [h1, h2, h3]
      · simp [h1, h2]
    · simp [h1]
  -- 内层归约
  have hReduce := charInnerReduce (q := q) a M N
  -- 单位类分组
  have hUcs := unitClassSum (q := q) a M N
  -- 组合: ℂ 值恒等式
  have hEq : (∑ χ : DirichletCharacter ℂ q, (‖S χ‖ : ℂ) ^ 2) =
      (q.totient : ℂ) * ∑ x : ZMod q, (if IsUnit x then 1 else 0) * (‖T x‖ : ℂ) ^ 2 := by
    calc
      (∑ χ : DirichletCharacter ℂ q, (‖S χ‖ : ℂ) ^ 2)
          = ∑ m ∈ Finset.Icc (M + 1) (M + N), ∑ n ∈ Finset.Icc (M + 1) (M + N),
              a m * star (a n) * (q.totient : ℂ) *
                (if IsUnit (m : ZMod q) then 1 else 0) *
                (if IsUnit (n : ZMod q) then 1 else 0) *
                (if (m : ZMod q) = (n : ZMod q) then 1 else 0) := by
            rw [hExp, hSwap, hSum]
      _ = (q.totient : ℂ) *
            ∑ m ∈ Finset.Icc (M + 1) (M + N),
              (if IsUnit (m : ZMod q) then 1 else 0) * a m *
                star (∑ n ∈ Finset.Icc (M + 1) (M + N),
                  a n * if (n : ZMod q) = (m : ZMod q) then 1 else 0) := hReduce
      _ = (q.totient : ℂ) * ∑ x : ZMod q, (if IsUnit x then 1 else 0) * (‖T x‖ : ℂ) ^ 2 := by
            rw [← hUcs]
  -- 转回 ℝ: 两边都是实数的 cast
  have hL : (∑ χ : DirichletCharacter ℂ q, (‖S χ‖ : ℂ) ^ 2) =
      (↑(∑ χ : DirichletCharacter ℂ q, ‖S χ‖ ^ 2) : ℂ) := by
    calc
      (∑ χ : DirichletCharacter ℂ q, (‖S χ‖ : ℂ) ^ 2)
          = ∑ χ : DirichletCharacter ℂ q, (↑(‖S χ‖ ^ 2) : ℂ) := by
            apply Finset.sum_congr rfl
            intro χ hχ
            norm_num
      _ = (↑(∑ χ : DirichletCharacter ℂ q, ‖S χ‖ ^ 2) : ℂ) := by
            simpa using (map_sum (algebraMap ℝ ℂ) (fun χ => ‖S χ‖ ^ 2) (Finset.univ)).symm
  have hR : (q.totient : ℂ) * ∑ x : ZMod q, (if IsUnit x then 1 else 0) * (‖T x‖ : ℂ) ^ 2 =
      (↑((q.totient : ℝ) * ∑ x : ZMod q, (if IsUnit x then 1 else 0) * ‖T x‖ ^ 2) : ℂ) := by
    calc
      (q.totient : ℂ) * ∑ x : ZMod q, (if IsUnit x then 1 else 0) * (‖T x‖ : ℂ) ^ 2
          = (↑(q.totient : ℝ) : ℂ) * ∑ x : ZMod q,
              ↑((if IsUnit x then (1 : ℝ) else 0) * ‖T x‖ ^ 2) := by
            apply congrArg (fun t : ℂ => (q.totient : ℂ) * t) ?_
            apply Finset.sum_congr rfl
            intro x hx
            by_cases h : IsUnit x
            · have h1 : (if IsUnit x then (1 : ℂ) else 0) = 1 := by simp [h]
              have h1r : (if IsUnit x then (1 : ℝ) else 0) = 1 := by simp [h]
              calc
                (if IsUnit x then (1 : ℂ) else 0) * (‖T x‖ : ℂ) ^ 2
                    = 1 * (‖T x‖ : ℂ) ^ 2 := by rw [h1]
                _ = (‖T x‖ : ℂ) ^ 2 := by rw [one_mul]
                _ = (↑(‖T x‖ ^ 2) : ℂ) := by norm_num
                _ = ↑((if IsUnit x then (1 : ℝ) else 0) * ‖T x‖ ^ 2) := by
                      rw [h1r]
                      norm_num
            · have h1 : (if IsUnit x then (1 : ℂ) else 0) = 0 := by simp [h]
              simp [h1, h]
      _ = (↑((q.totient : ℝ) * ∑ x : ZMod q, (if IsUnit x then 1 else 0) * ‖T x‖ ^ 2) : ℂ) := by
            rw [← Complex.ofReal_sum]
            rw [← Complex.ofReal_mul]
  have hReal : (∑ χ : DirichletCharacter ℂ q, ‖S χ‖ ^ 2) =
      (q.totient : ℝ) * ∑ x : ZMod q, (if IsUnit x then 1 else 0) * ‖T x‖ ^ 2 := by
    have h := hL.symm.trans hEq
    have h2 := h.trans hR
    exact Complex.ofReal_inj.mp h2
  -- 去掉 [IsUnit x] 因子
  have hLe : (q.totient : ℝ) * ∑ x : ZMod q, (if IsUnit x then 1 else 0) * ‖T x‖ ^ 2 ≤
      (q.totient : ℝ) * ∑ x : ZMod q, ‖T x‖ ^ 2 := by
    have hterm : ∀ x : ZMod q, (if IsUnit x then 1 else 0) * ‖T x‖ ^ 2 ≤ ‖T x‖ ^ 2 := by
      intro x
      by_cases h : IsUnit x
      · simp [h]
      · simp [h]
    have hsum : (∑ x : ZMod q, (if IsUnit x then 1 else 0) * ‖T x‖ ^ 2) ≤
        ∑ x : ZMod q, ‖T x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      exact hterm x
    exact mul_le_mul_of_nonneg_left hsum (by exact_mod_cast Nat.zero_le (q.totient))
  -- 结论
  calc
    (∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * χ (n : ZMod q)‖ ^ 2)
        = ∑ χ : DirichletCharacter ℂ q, ‖S χ‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro χ hχ
          rfl
    _ = (q.totient : ℝ) * ∑ x : ZMod q, (if IsUnit x then 1 else 0) * ‖T x‖ ^ 2 := hReal
    _ ≤ (q.totient : ℝ) * ∑ x : ZMod q, ‖T x‖ ^ 2 := hLe
    _ = (q.totient : ℝ) * ∑ x : ZMod q,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * if (n : ZMod q) = x then 1 else 0‖ ^ 2 := by
          apply congrArg (fun t : ℝ => (q.totient : ℝ) * t) ?_
          apply Finset.sum_congr rfl
          intro x hx
          rfl

/-! ## 4. 有理点集 well-spaced 与乘法大筛 -/

/-- 有理点集 `X_Q = {r/q : 1 ≤ q ≤ Q, 0 ≤ r < q} ⊆ [0,1)`. -/
noncomputable def rationalPoints (Q : ℕ) : Finset ℝ :=
  (Finset.Icc 1 Q).biUnion (fun q => (Finset.range q).image (fun r : ℕ => (r : ℝ) / (q : ℝ)))

/-- 两个不同模 1 有理数的距离 ≥ 1/(q₁q₂). -/
theorem rationals_distToInt_ge {q₁ r₁ q₂ r₂ : ℕ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hr₁ : r₁ < q₁) (hr₂ : r₂ < q₂)
    (hne : (r₁ : ℝ) / (q₁ : ℝ) ≠ (r₂ : ℝ) / (q₂ : ℝ)) :
    1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤
      distToInt ((r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)) := by
  -- 两个点都在 [0,1), 故差非整数
  have hx0 : 0 ≤ (r₁ : ℝ) / (q₁ : ℝ) := by positivity
  have hx1 : (r₁ : ℝ) / (q₁ : ℝ) < 1 := by
    exact (div_lt_one (by exact_mod_cast hq₁)).mpr (by exact_mod_cast hr₁)
  have hy0 : 0 ≤ (r₂ : ℝ) / (q₂ : ℝ) := by positivity
  have hy1 : (r₂ : ℝ) / (q₂ : ℝ) < 1 := by
    exact (div_lt_one (by exact_mod_cast hq₂)).mpr (by exact_mod_cast hr₂)
  have hnotint : ¬ ∃ k : ℤ, (k : ℝ) = (r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) := by
    intro hk
    rcases hk with ⟨k, hk⟩
    -- |x − y| < 1 且 x ≠ y ⟹ k = 0 ⟹ x = y 矛盾
    have hlt : |(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)| < 1 := by
      -- 0 ≤ x,y < 1 ⟹ |x−y| < 1
      have hxy : (r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) < 1 := by linarith
      have hxy' : -1 < (r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) := by linarith
      rw [abs_lt]
      exact ⟨hxy', hxy⟩
    have hkabs : |(k : ℝ)| < 1 := by
      calc
        |(k : ℝ)| = |(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)| := by
          exact congrArg abs hk
        _ < 1 := hlt
    have hk0 : k = 0 := by
      -- |k| < 1 且 k : ℤ ⟹ k = 0
      have hkz : (k.natAbs : ℝ) < 1 := by
        -- |k| = ↑k.natAbs
        have hcast : |(k : ℝ)| = ((k.natAbs : ℕ) : ℝ) := by
          rw [← Int.cast_abs]
          congr 1
          exact Int.abs_eq_natAbs k
        calc
          (k.natAbs : ℝ) = |(k : ℝ)| := hcast.symm
          _ < 1 := hkabs
      have hk0' : k.natAbs = 0 := by
        -- 0 ≤ k.natAbs < 1 ⟹ = 0
        have hlt' : k.natAbs < 1 := by exact_mod_cast hkz
        omega
      exact Int.natAbs_eq_zero.mp hk0'
    -- x = y 矛盾
    apply hne
    have hxy : (r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) = 0 := by
      rw [← hk, hk0]
      norm_num
    linarith
  -- 对任意整数 k, |x − y − k| ≥ 1/(q₁q₂)
  have hk : ∀ k : ℤ, 1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤
      |(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) - (k : ℝ)| := by
    intro k
    -- x − y − k = (r₁q₂ − r₂q₁ − k q₁q₂)/(q₁q₂), 分子非零整数
    have hnum : ((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ) ≠ 0 := by
      intro hz
      -- 分子 = 0 ⟹ x − y = k（交叉相乘）—— 与 hnotint 矛盾
      apply hnotint
      refine ⟨k, ?_⟩
      -- (r₁:ℝ)/(q₁:ℝ) − (r₂:ℝ)/(q₂:ℝ) = (r₁q₂ − r₂q₁)/(q₁q₂) = k
      have hcross : ((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) : ℤ) = k * ((q₁ : ℤ) * (q₂ : ℤ)) := by
        linarith
      -- 转成 ℝ
      have hcrossR : ((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) : ℝ) =
          (k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℝ) := by exact_mod_cast hcross
      -- 目标: (r₁:ℝ)/(q₁:ℝ) − (r₂:ℝ)/(q₂:ℝ) = k
      have htarget : (r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) = (k : ℝ) := by
        have hmain : ((r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)) * ((q₁ : ℝ) * (q₂ : ℝ)) =
            (k : ℝ) * ((q₁ : ℝ) * (q₂ : ℝ)) := by
          calc
            ((r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)) * ((q₁ : ℝ) * (q₂ : ℝ))
                = (r₁ : ℝ) * (q₂ : ℝ) - (r₂ : ℝ) * (q₁ : ℝ) := by
                  field_simp [hq₁.ne', hq₂.ne']
            _ = (k : ℝ) * ((q₁ : ℝ) * (q₂ : ℝ)) := hcrossR
        have hden : (q₁ : ℝ) * (q₂ : ℝ) ≠ 0 := by positivity
        have hmain' : (q₁ : ℝ) * (q₂ : ℝ) * ((r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)) =
            (q₁ : ℝ) * (q₂ : ℝ) * (k : ℝ) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
        exact mul_left_cancel₀ hden hmain'
      exact htarget.symm
    -- |x − y − k| = |分子|/(q₁q₂) ≥ 1/(q₁q₂)
    have habs : |(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) - (k : ℝ)| =
        |(((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ) : ℝ)| /
          ((q₁ : ℝ) * (q₂ : ℝ)) := by
      have hnumR : (r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) - (k : ℝ) =
          (((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ) : ℝ) /
            ((q₁ : ℝ) * (q₂ : ℝ)) := by
        field_simp [hq₁.ne', hq₂.ne']
        norm_num [Int.cast_mul, Int.cast_sub]
        ring
      have hden : 0 < (q₁ : ℝ) * (q₂ : ℝ) := mul_pos (by exact_mod_cast hq₁) (by exact_mod_cast hq₂)
      rw [hnumR, abs_div, abs_of_nonneg (le_of_lt hden)]
    have hnumR : |(((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ) : ℝ)| ≠ 0 := by
      have hn : ((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ) ≠ 0 := hnum
      have hz : ((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℝ) ≠ 0 := by
        exact_mod_cast hn
      intro habs
      have h0 : ((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℝ) = 0 := by
        simpa using (abs_eq_zero.mp habs)
      exact hz h0
    have hge1 : 1 ≤ |(((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ) : ℝ)| := by
      -- 非零整数 ⟹ 绝对值 ≥ 1
      have hz : ((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ) ≠ 0 := hnum
      have hz' : ((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ).natAbs ≠ 0 :=
        Int.natAbs_ne_zero.mpr hz
      have hz1 : 1 ≤ ((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ).natAbs := by
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hz')
      -- |↑n| = ↑n.natAbs ≥ 1
      have hcast : |(((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ) : ℝ)| =
          (((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ).natAbs : ℝ) := by
        rw [← Int.cast_abs]
        congr 1
        exact Int.abs_eq_natAbs (r₁ * q₂ - r₂ * q₁ - k * (q₁ * q₂) : ℤ)
      rw [hcast]
      exact_mod_cast hz1
    rw [habs]
    -- |分子|/(q₁q₂) ≥ 1/(q₁q₂) ⟺ |分子| ≥ 1
    have hden : 0 < (q₁ : ℝ) * (q₂ : ℝ) := mul_pos (by exact_mod_cast hq₁) (by exact_mod_cast hq₂)
    have hpos : 0 ≤ 1 / ((q₁ : ℝ) * (q₂ : ℝ)) := one_div_nonneg.mpr (le_of_lt hden)
    calc
      1 / ((q₁ : ℝ) * (q₂ : ℝ))
          ≤ |(((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ) : ℝ)| *
              (1 / ((q₁ : ℝ) * (q₂ : ℝ))) := by
            simpa using (mul_le_mul_of_nonneg_right hge1 hpos)
      _ = |(((r₁ : ℤ) * (q₂ : ℤ) - (r₂ : ℤ) * (q₁ : ℤ) - k * ((q₁ : ℤ) * (q₂ : ℤ)) : ℤ) : ℝ)| /
            ((q₁ : ℝ) * (q₂ : ℝ)) := by ring
  -- distToInt z = min(fract z, 1−fract z), 且 |z−⌊z⌋|, |z−(⌊z⌋+1)| ≥ 1/(q₁q₂)
  let z : ℝ := (r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)
  have hz1 : 1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤ |z - (⌊z⌋ : ℝ)| := by
    change 1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤
      |(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) -
        (⌊(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)⌋ : ℝ)|
    exact hk (⌊(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)⌋)
  have hz2 : 1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤ |z - ((⌊z⌋ + 1 : ℤ) : ℝ)| := by
    change 1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤
      |(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ) -
        ((⌊(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)⌋ + 1 : ℤ) : ℝ)|
    exact hk (⌊(r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)⌋ + 1)
  -- |z − ⌊z⌋| = fract z, |z − (⌊z⌋+1)| = 1 − fract z
  have hf1 : |z - (⌊z⌋ : ℝ)| = Int.fract z := by
    -- fract z = z − ⌊z⌋ ≥ 0
    have hzge : 0 ≤ z - (⌊z⌋ : ℝ) := by
      rw [Int.self_sub_floor]
      exact Int.fract_nonneg z
    calc
      |z - (⌊z⌋ : ℝ)| = z - (⌊z⌋ : ℝ) := abs_of_nonneg hzge
      _ = Int.fract z := by simpa using (Int.self_sub_floor z)
  have hf2 : |z - ((⌊z⌋ + 1 : ℤ) : ℝ)| = 1 - Int.fract z := by
    -- ⌊z⌋+1 − z = 1 − fract z ≥ 0
    have hzle : 0 ≤ ((⌊z⌋ + 1 : ℤ) : ℝ) - z := by
      -- z < ⌊z⌋ + 1
      have hlt : z < (⌊z⌋ : ℝ) + 1 := by
        -- Int.lt_floor_add_one
        have := Int.lt_floor_add_one z
        -- z < ↑⌊z⌋ + 1
        simpa using this
      have hle : (⌊z⌋ : ℝ) + 1 ≤ ((⌊z⌋ + 1 : ℤ) : ℝ) := by norm_num
      linarith
    have habs : |z - ((⌊z⌋ + 1 : ℤ) : ℝ)| = ((⌊z⌋ + 1 : ℤ) : ℝ) - z := by
      rw [abs_sub_comm]
      exact abs_of_nonneg hzle
    rw [habs]
    -- (⌊z⌋+1) − z = 1 − fract z
    have hfz : z = Int.fract z + (⌊z⌋ : ℝ) := (Int.fract_add_floor z).symm
    calc
      ((⌊z⌋ + 1 : ℤ) : ℝ) - z = ((⌊z⌋ : ℝ) + 1) - z := by norm_num
      _ = ((⌊z⌋ : ℝ) + 1) - (Int.fract z + (⌊z⌋ : ℝ)) := by
            conv_lhs =>
              arg 2
              rw [hfz]
      _ = 1 - Int.fract z := by ring
  -- distToInt z = min(fract z, 1 − fract z) ≥ 1/(q₁q₂)
  dsimp [distToInt]
  rw [le_min_iff]
  constructor
  · -- fract z ≥ 1/(q₁q₂)
    rw [← hf1]
    exact hz1
  · -- 1 − fract z ≥ 1/(q₁q₂)
    rw [← hf2]
    exact hz2

/-- 有理点集 `X_Q = {r/q : 1 ≤ q ≤ Q, 0 ≤ r < q}` 是 `1/Q²`-well-spaced. -/
theorem rationalPoints_wellSpaced (Q : ℕ) (hQ : 0 < Q) :
    wellSpacedReal (rationalPoints Q) (1 / (Q : ℝ) ^ 2) := by
  intro x hx y hy hxy
  rcases (Finset.mem_biUnion.mp hx) with ⟨q₁, hq₁, hx'⟩
  rcases (Finset.mem_image.mp hx') with ⟨r₁, hr₁, rfl⟩
  rcases (Finset.mem_biUnion.mp hy) with ⟨q₂, hq₂, hy'⟩
  rcases (Finset.mem_image.mp hy') with ⟨r₂, hr₂, rfl⟩
  have hq₁pos : 0 < q₁ := (Finset.mem_Icc.mp hq₁).1
  have hq₂pos : 0 < q₂ := (Finset.mem_Icc.mp hq₂).1
  have hq₁Q : q₁ ≤ Q := (Finset.mem_Icc.mp hq₁).2
  have hq₂Q : q₂ ≤ Q := (Finset.mem_Icc.mp hq₂).2
  have hr₁' : r₁ < q₁ := Finset.mem_range.mp hr₁
  have hr₂' : r₂ < q₂ := Finset.mem_range.mp hr₂
  have hd : 1 / ((q₁ : ℝ) * (q₂ : ℝ)) ≤
      distToInt ((r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)) :=
    rationals_distToInt_ge hq₁pos hq₂pos hr₁' hr₂' hxy
  have hq₁q₂ : (q₁ : ℝ) * (q₂ : ℝ) ≤ (Q : ℝ) * (Q : ℝ) := by
    have h₁ : (q₁ : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq₁Q
    have h₂ : (q₂ : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hq₂Q
    exact mul_le_mul h₁ h₂ (by positivity) (by positivity)
  have hden₁ : 0 < (q₁ : ℝ) * (q₂ : ℝ) := mul_pos (by exact_mod_cast hq₁pos) (by exact_mod_cast hq₂pos)
  have hQinv : 1 / ((Q : ℝ) * (Q : ℝ)) ≤ 1 / ((q₁ : ℝ) * (q₂ : ℝ)) :=
    one_div_le_one_div_of_le hden₁ hq₁q₂
  have hQ2 : (Q : ℝ) ^ 2 = (Q : ℝ) * (Q : ℝ) := by ring
  calc
    1 / (Q : ℝ) ^ 2 = 1 / ((Q : ℝ) * (Q : ℝ)) := by rw [hQ2]
    _ ≤ 1 / ((q₁ : ℝ) * (q₂ : ℝ)) := hQinv
    _ ≤ distToInt ((r₁ : ℝ) / (q₁ : ℝ) - (r₂ : ℝ) / (q₂ : ℝ)) := hd
