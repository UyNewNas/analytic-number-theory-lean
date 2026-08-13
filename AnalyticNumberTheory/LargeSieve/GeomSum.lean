/-
! # AnalyticNumberTheory.LargeSieve.GeomSum

## 几何级数界 (Geometric-sum bound)

加法大筛 (Montgomery) 证明的第一块解析台阶: 对 `e(x) = exp(2πix)` 与
`‖x‖` (x 到最近整数的距离, 用 `Int.fract` 表示),

  |Σ_{n<N} e(nx)| ≤ min(N, 1/(2‖x‖)).

本模块给出完整证明: 平凡界 `≤ N` (每项模长 1) 与非平凡界 `≤ 1/(2‖x‖)`
(几何级数公式 + `|e(x)−1| = 2|sin(πx)|` + `|sin(πt)| ≥ 2·min(t,1−t)`).

参考: Iwaniec--Kowalski, "Analytic Number Theory" (2004), Ch. 7 Lemma 7.6;
Davenport, "Multiplicative Number Theory", Ch. 27.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Order.Interval.Finset.SuccPred
import Mathlib.Tactic

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators

noncomputable section

/-! ## 1. 到最近整数的距离 -/

/-- 分数部分 `x − ⌊x⌋ ∈ [0,1)`. -/
theorem fract_nonneg (x : ℝ) : 0 ≤ Int.fract x := by
  rw [← Int.self_sub_floor x]
  exact sub_nonneg.mpr (Int.floor_le x)

/-- 分数部分 `< 1`. -/
theorem fract_lt_one (x : ℝ) : Int.fract x < 1 := by
  rw [← Int.self_sub_floor x]
  exact sub_lt_iff_lt_add.mpr (by rw [add_comm]; exact Int.lt_floor_add_one x)

/-- 到最近整数的距离 `‖x‖ = min(x − ⌊x⌋, 1 − (x − ⌊x⌋))`. -/
noncomputable def distToInt (x : ℝ) : ℝ := min (Int.fract x) (1 - Int.fract x)

theorem distToInt_nonneg (x : ℝ) : 0 ≤ distToInt x := by
  dsimp [distToInt]
  exact le_min (fract_nonneg x) (by linarith [fract_lt_one x])

theorem distToInt_le_half (x : ℝ) : distToInt x ≤ 1 / 2 := by
  dsimp [distToInt]
  by_cases h : Int.fract x ≤ 1 / 2
  · exact le_trans (min_le_left _ _) h
  · have h' : 1 - Int.fract x ≤ 1 / 2 := by linarith
    exact le_trans (min_le_right _ _) h'

/-! ## 2. 加法特征与几何级数 -/

/-- `e(x) = exp(2πix)`: 加法特征 (ℝ 参数化). -/
noncomputable def charReal (x : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * (x : ℂ)) * Complex.I)

/-- `e(nx) = e(x)^n` (`n : ℕ`): 由 `Complex.exp_nsmul` 得到. -/
theorem charReal_nat_mul (n : ℕ) (x : ℝ) : charReal (n * x) = (charReal x) ^ n := by
  dsimp [charReal]
  rw [show (2 * Real.pi * ((n * x : ℝ) : ℂ)) * Complex.I =
      n • ((2 * Real.pi * (x : ℂ)) * Complex.I) by
        rw [nsmul_eq_mul]
        norm_num [Complex.ofReal_mul]
        ring]
  rw [Complex.exp_nsmul]

/-- `e` 以 1 为周期: `e(x+1) = e(x)`, 由 `exp(2πi) = 1` 得到. -/
theorem charReal_periodic : Function.Periodic charReal 1 := by
  intro x
  dsimp [charReal]
  rw [show (2 * Real.pi * ((x + 1 : ℝ) : ℂ)) * Complex.I =
      (2 * Real.pi * (x : ℂ)) * Complex.I + 2 * Real.pi * Complex.I by
        rw [Complex.ofReal_add, Complex.ofReal_one]
        ring]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I]
  ring

/-- `e(a + b) = e(a)·e(b)`: 特征作为 (ℝ,+) → (ℂ,·) 的群同态. -/
theorem charReal_add (a b : ℝ) : charReal (a + b) = charReal a * charReal b := by
  dsimp [charReal]
  rw [show (2 * Real.pi * ((a + b : ℝ) : ℂ)) * Complex.I =
      (2 * Real.pi * (a : ℂ)) * Complex.I + (2 * Real.pi * (b : ℂ)) * Complex.I by
        rw [Complex.ofReal_add]
        ring]
  rw [Complex.exp_add]

/-- 参数重排: `(2π·c)·I = c·(2π·I)` (纯多项式, 对任意实数 `c` 成立). -/
theorem mul_charReal_arg (c : ℂ) :
    (2 * Real.pi * c) * Complex.I = c * (2 * Real.pi * Complex.I) := by
  ring

/-- 特征只依赖模 1 类: `e(x) = e(fract x)`. -/
theorem charReal_eq_charReal_fract (x : ℝ) : charReal x = charReal (Int.fract x) := by
  have hx : x = Int.fract x + (⌊x⌋ : ℝ) := (Int.fract_add_floor x).symm
  conv_lhs => rw [hx]
  rw [charReal_add]
  have he : charReal ((⌊x⌋ : ℝ)) = 1 := by
    dsimp [charReal]
    rw [show (2 * Real.pi * (⌊x⌋ : ℂ)) * Complex.I =
        (⌊x⌋ : ℂ) * (2 * Real.pi * Complex.I) by
          exact mul_charReal_arg (⌊x⌋ : ℂ)]
    rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
  rw [he, mul_one]

/-- 几何级数恒等式: `Σ_{n<N} e(nx) = (e(Nx)−1)/(e(x)−1)` (`e(x) ≠ 1`). -/
theorem geomSum_exp_eq_geomSeries (N : ℕ) {x : ℝ} (hz : charReal x ≠ 1) :
    (∑ n ∈ Finset.range N, charReal (n * x)) = (charReal (N * x) - 1) / (charReal x - 1) := by
  rw [Finset.sum_congr rfl (fun n hn => charReal_nat_mul n x)]
  rw [charReal_nat_mul N x]
  exact geom_sum_eq hz N

/-- **平凡界**: `|Σ_{n<N} e(nx)| ≤ N` (每项模长 1). -/
theorem geomSum_exp_bound_trivial (N : ℕ) (x : ℝ) :
    ‖∑ n ∈ Finset.range N, charReal (n * x)‖ ≤ N := by
  have hz : ∀ n : ℕ, ‖charReal (n * x)‖ = 1 := by
    intro n
    dsimp [charReal]
    simpa using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (n * x : ℝ))
  calc
    ‖∑ n ∈ Finset.range N, charReal (n * x)‖ ≤ ∑ n ∈ Finset.range N, ‖charReal (n * x)‖ := by
      exact norm_sum_le (Finset.range N) (fun n => charReal (n * x))
    _ = ∑ n ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hz n]
    _ = N := by simp

/-! ## 3. 三角恒等式 -/

/-- `|e(x) − 1| = 2|sin(πx)|`: `e(x) = exp(πix)²` 与
`exp(πix) − exp(−πix) = 2i·sin(πx)` 的组合. -/
theorem abs_charReal_sub_one (x : ℝ) :
    ‖charReal x - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
  have h1 : charReal x = (Complex.exp (Real.pi * (x : ℂ) * Complex.I)) ^ 2 := by
    dsimp [charReal]
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  have h2 : (1 : ℂ) = Complex.exp (Real.pi * (x : ℂ) * Complex.I) *
      Complex.exp (-(Real.pi * (x : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]
    simp
  have hsq : charReal x - 1 = Complex.exp (Real.pi * (x : ℂ) * Complex.I) *
      (Complex.exp (Real.pi * (x : ℂ) * Complex.I) -
        Complex.exp (-(Real.pi * (x : ℂ) * Complex.I))) := by
    rw [h1, h2]
    ring
  have hsub : Complex.exp (Real.pi * (x : ℂ) * Complex.I) -
      Complex.exp (-(Real.pi * (x : ℂ) * Complex.I)) =
      2 * Complex.I * Complex.sin (Real.pi * (x : ℂ)) := by
    rw [Complex.exp_mul_I]
    rw [show -(Real.pi * (x : ℂ) * Complex.I) = -(Real.pi * (x : ℂ)) * Complex.I by ring]
    rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  calc
    ‖charReal x - 1‖ = ‖Complex.exp (Real.pi * (x : ℂ) * Complex.I) *
        (Complex.exp (Real.pi * (x : ℂ) * Complex.I) -
          Complex.exp (-(Real.pi * (x : ℂ) * Complex.I)))‖ := by rw [hsq]
    _ = ‖Complex.exp (Real.pi * (x : ℂ) * Complex.I)‖ *
          ‖Complex.exp (Real.pi * (x : ℂ) * Complex.I) -
            Complex.exp (-(Real.pi * (x : ℂ) * Complex.I))‖ := by rw [norm_mul]
    _ = 1 * ‖2 * Complex.I * Complex.sin (Real.pi * (x : ℂ))‖ := by
          rw [hsub]
          congr 1
          simpa using Complex.norm_exp_ofReal_mul_I (Real.pi * x)
    _ = 2 * |Real.sin (Real.pi * x)| := by
          have hsin : Complex.sin (Real.pi * (x : ℂ)) = (Real.sin (Real.pi * x) : ℂ) := by
            have harg : Real.pi * (x : ℂ) = ((Real.pi * x : ℝ) : ℂ) := by
              rw [Complex.ofReal_mul]
            rw [harg, ← Complex.ofReal_sin]
          rw [norm_mul, norm_mul, Complex.norm_I, hsin, Complex.norm_real]
          norm_num

/-- `|sin(πt)| ≥ 2·min(t, 1−t)` 对 `t ∈ [0,1]`: 在 `[0,1/2]` 上
`sin(πt) ≥ 2t`, 在 `[1/2,1]` 上用反射 `sin(πt) = sin(π(1−t))`. -/
theorem abs_sin_pi_mul_ge_two_min (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    2 * min t (1 - t) ≤ |Real.sin (Real.pi * t)| := by
  by_cases ht : t ≤ 1 / 2
  · have hmin : min t (1 - t) = t := min_eq_left (by linarith)
    have hpt0 : 0 ≤ Real.pi * t := mul_nonneg Real.pi_pos.le ht0
    have hpt1 : Real.pi * t ≤ Real.pi / 2 := by nlinarith [Real.pi_pos, ht]
    have hs : 2 / Real.pi * (Real.pi * t) ≤ Real.sin (Real.pi * t) :=
      Real.mul_le_sin hpt0 hpt1
    have h2t : 2 * t ≤ Real.sin (Real.pi * t) := by
      field_simp [Real.pi_ne_zero] at hs ⊢
      exact hs
    have hnonneg : 0 ≤ Real.sin (Real.pi * t) := le_trans (by nlinarith [ht0]) h2t
    rw [hmin, abs_of_nonneg hnonneg]
    exact h2t
  · have hmin : min t (1 - t) = 1 - t := min_eq_right (by linarith)
    have hs0 : 0 ≤ 1 - t := by linarith
    have hs1 : 1 - t ≤ 1 / 2 := by linarith
    have hpt0 : 0 ≤ Real.pi * (1 - t) := mul_nonneg Real.pi_pos.le hs0
    have hpt1 : Real.pi * (1 - t) ≤ Real.pi / 2 := by nlinarith [Real.pi_pos, hs1]
    have hs : 2 / Real.pi * (Real.pi * (1 - t)) ≤ Real.sin (Real.pi * (1 - t)) :=
      Real.mul_le_sin hpt0 hpt1
    have h2s : 2 * (1 - t) ≤ Real.sin (Real.pi * (1 - t)) := by
      field_simp [Real.pi_ne_zero] at hs ⊢
      exact hs
    have hreflect : Real.sin (Real.pi * t) = Real.sin (Real.pi * (1 - t)) := by
      rw [show Real.pi * t = Real.pi - Real.pi * (1 - t) by ring]
      rw [Real.sin_pi_sub]
    have hnonneg : 0 ≤ Real.sin (Real.pi * (1 - t)) := le_trans (by nlinarith [hs0]) h2s
    rw [hmin, hreflect, abs_of_nonneg hnonneg]
    exact h2s

/-! ## 4. 非平凡界 -/

/-- `e(x) ≠ 1` 当 `x ∉ ℤ`: 由 `|e(x)−1| = 2|sin(π·fract x)| > 0` 得到. -/
theorem charReal_ne_one_of_not_int {x : ℝ} (hx : ¬ ∃ k : ℤ, (k : ℝ) = x) :
    charReal x ≠ 1 := by
  have hx' : Int.fract x ≠ 0 := by
    intro hf
    apply hx
    refine ⟨⌊x⌋, ?_⟩
    rw [← Int.fract_add_floor x, hf]
    norm_num
  have hpos : 0 < ‖charReal x - 1‖ := by
    rw [charReal_eq_charReal_fract, abs_charReal_sub_one]
    have ht0 : 0 < Int.fract x := lt_of_le_of_ne (fract_nonneg x) (Ne.symm hx')
    have hs : 0 < Real.sin (Real.pi * Int.fract x) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht0)
        (by nlinarith [fract_lt_one x, Real.pi_pos])
    have hsinabs : 0 < |Real.sin (Real.pi * Int.fract x)| := abs_pos.mpr (ne_of_gt hs)
    nlinarith [hsinabs]
  intro h
  have hzero : ‖charReal x - 1‖ = 0 := by simp [h]
  exact (ne_of_gt hpos) hzero

/-- **几何级数界 (非平凡部分)**: 对 `x ∉ ℤ`,
  |Σ_{n<N} e(nx)| ≤ 1/(2‖x‖).
由几何级数公式、`|e(x)−1| = 2|sin(π·fract x)|` 与
`|sin(πt)| ≥ 2·min(t,1−t)` 组合得到. -/
theorem geomSum_exp_bound_far (N : ℕ) {x : ℝ} (hx : ¬ ∃ k : ℤ, (k : ℝ) = x) :
    ‖∑ n ∈ Finset.range N, charReal (n * x)‖ ≤ 1 / (2 * distToInt x) := by
  have hz : charReal x ≠ 1 := charReal_ne_one_of_not_int hx
  have hx' : Int.fract x ≠ 0 := by
    intro hf
    apply hx
    refine ⟨⌊x⌋, ?_⟩
    rw [← Int.fract_add_floor x, hf]
    norm_num
  have hs : 0 < |Real.sin (Real.pi * Int.fract x)| := by
    have ht0 : 0 < Int.fract x := lt_of_le_of_ne (fract_nonneg x) (Ne.symm hx')
    have hs' : 0 < Real.sin (Real.pi * Int.fract x) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht0)
        (by nlinarith [fract_lt_one x, Real.pi_pos])
    exact abs_pos.mpr (ne_of_gt hs')
  have hd : 0 < 2 * distToInt x := by
    have hd0 : 0 < distToInt x := by
      dsimp [distToInt]
      exact lt_min (lt_of_le_of_ne (fract_nonneg x) (Ne.symm hx'))
        (by linarith [fract_lt_one x])
    nlinarith
  have hsin : 2 * distToInt x ≤ |Real.sin (Real.pi * Int.fract x)| := by
    dsimp [distToInt]
    exact abs_sin_pi_mul_ge_two_min (Int.fract x) (fract_nonneg x) (le_of_lt (fract_lt_one x))
  calc
    ‖∑ n ∈ Finset.range N, charReal (n * x)‖
        = ‖(charReal (N * x) - 1) / (charReal x - 1)‖ := by
          rw [geomSum_exp_eq_geomSeries N hz]
    _ = ‖charReal (N * x) - 1‖ / ‖charReal x - 1‖ := by rw [norm_div]
    _ ≤ 2 / ‖charReal x - 1‖ := by
          have htop : ‖charReal (N * x) - 1‖ ≤ 2 := by
            have htop' : ‖charReal (N * x) - 1‖ ≤ ‖charReal (N * x)‖ + ‖(1 : ℂ)‖ :=
              norm_sub_le _ _
            have hN1 : ‖charReal (N * x)‖ = 1 := by
              dsimp [charReal]
              simpa using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (N * x : ℝ))
            have hone : ‖(1 : ℂ)‖ = 1 := by norm_num
            nlinarith [htop', hN1, hone]
          have hb : 0 < ‖charReal x - 1‖ := by
            exact norm_pos_iff.mpr (sub_ne_zero.mpr hz)
          exact div_le_div_of_nonneg_right htop (le_of_lt hb)
    _ = 1 / |Real.sin (Real.pi * Int.fract x)| := by
          have hz1' : ‖charReal x - 1‖ = 2 * |Real.sin (Real.pi * Int.fract x)| := by
            rw [charReal_eq_charReal_fract x, abs_charReal_sub_one]
          rw [hz1']
          field_simp [hs]
    _ ≤ 1 / (2 * distToInt x) := by
          exact one_div_le_one_div_of_le hd hsin

/-- **几何级数界**: 对任意 `N, x`,
  |Σ_{n<N} e(nx)| ≤ min(N, 1/(2‖x‖))
的两个组成部分 (平凡界与非平凡界). -/
theorem geomSum_exp_bound (N : ℕ) (x : ℝ) :
    ‖∑ n ∈ Finset.range N, charReal (n * x)‖ ≤ N ∧
      ((¬ ∃ k : ℤ, (k : ℝ) = x) →
        ‖∑ n ∈ Finset.range N, charReal (n * x)‖ ≤ 1 / (2 * distToInt x)) := by
  constructor
  · exact geomSum_exp_bound_trivial N x
  · intro hx
    exact geomSum_exp_bound_far N hx

/-! ## 5. 区间几何级数界 -/

/-- 特征与负参数: `e(−x) = star(e(x))`, 由 `exp(conj z) = conj(exp z)` 得到. -/
theorem charReal_neg (x : ℝ) : charReal (-x) = star (charReal x) := by
  dsimp [charReal]
  rw [show (2 * Real.pi * ((-x : ℝ) : ℂ)) * Complex.I =
      -((2 * Real.pi * (x : ℂ)) * Complex.I) by
        rw [Complex.ofReal_neg]
        ring]
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul (starRingEnd ℂ)]
  rw [map_mul (starRingEnd ℂ)]
  rw [map_mul (starRingEnd ℂ)]
  rw [Complex.conj_ofNat]
  rw [Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- 特征的性质: `e(a − b) = e(a)·star(e(b))` (群同态 + 共轭). -/
theorem charReal_sub (a b : ℝ) : charReal (a - b) = charReal a * star (charReal b) := by
  rw [sub_eq_add_neg, charReal_add, charReal_neg]

/-- 区间 `(M, M+N]` 上的指数和 `Σ_{M<n≤M+N} e(nx)` (`n : ℤ`, 平移区间). -/
noncomputable def charRealSubIcc (M : ℤ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (M + 1) (M + N), charReal ((n : ℝ) * x)

lemma charRealSubIcc_succ (M : ℤ) (N : ℕ) (x : ℝ) :
    charRealSubIcc M (N + 1) x =
      charRealSubIcc M N x + charReal (((M + N + 1 : ℤ) : ℝ) * x) := by
  dsimp [charRealSubIcc]
  have hIcc : Finset.Icc (M + 1) (M + (N + 1) : ℤ) =
      insert (M + N + 1) (Finset.Icc (M + 1) (M + N)) := by
    ext n
    simp [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hmem : M + N + 1 ∉ Finset.Icc (M + 1) (M + N) := by
    rw [Finset.mem_Icc]
    omega
  rw [hIcc, Finset.sum_insert hmem]
  simp [add_comm]

/-- **区间指数和因子化**: `Σ_{M<n≤M+N} e(nx) = e((M+1)x)·Σ_{k<N} e(kx)`. -/
theorem charRealSubIcc_eq_shift (M : ℤ) (N : ℕ) (x : ℝ) :
    charRealSubIcc M N x =
      charReal (((M + 1 : ℤ) : ℝ) * x) * ∑ k ∈ Finset.range N, charReal ((k : ℝ) * x) := by
  induction N with
  | zero =>
      dsimp [charRealSubIcc]
      simp
  | succ N ih =>
      rw [charRealSubIcc_succ, ih]
      rw [Finset.sum_range_succ]
      have htop : charReal (((M + N + 1 : ℤ) : ℝ) * x) =
          charReal (((M + 1 : ℤ) : ℝ) * x) * charReal ((N : ℝ) * x) := by
        have hz : (((M + N + 1 : ℤ) : ℝ) * x) =
            (((M + 1 : ℤ) : ℝ) * x) + ((N : ℝ) * x) := by
          have hzℤ : (M + N + 1 : ℤ) = (M + 1) + (N : ℤ) := by omega
          rw [hzℤ]
          push_cast
          ring
        rw [hz, charReal_add]
      rw [htop]
      ring

/-- **区间指数和 (平凡界)**: `|Σ_{M<n≤M+N} e(nx)| ≤ N`. -/
theorem geomSum_exp_bound_Icc_trivial (M : ℤ) (N : ℕ) (x : ℝ) :
    ‖charRealSubIcc M N x‖ ≤ N := by
  rw [charRealSubIcc_eq_shift]
  have hunit : ‖charReal (((M + 1 : ℤ) : ℝ) * x)‖ = 1 := by
    dsimp [charReal]
    simpa using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (((M + 1 : ℤ) : ℝ) * x))
  calc
    ‖charReal (((M + 1 : ℤ) : ℝ) * x) *
        ∑ k ∈ Finset.range N, charReal ((k : ℝ) * x)‖
        ≤ ‖charReal (((M + 1 : ℤ) : ℝ) * x)‖ *
            ‖∑ k ∈ Finset.range N, charReal ((k : ℝ) * x)‖ := by
          exact norm_mul_le _ _
    _ = ‖∑ k ∈ Finset.range N, charReal ((k : ℝ) * x)‖ := by rw [hunit, one_mul]
    _ ≤ N := by
          simpa using geomSum_exp_bound_trivial N x

/-- **区间指数和 (非平凡界)**: 对 `x ∉ ℤ`,
  `|Σ_{M<n≤M+N} e(nx)| ≤ 1/(2‖x‖)`. -/
theorem geomSum_exp_bound_Icc_far (M : ℤ) (N : ℕ) {x : ℝ}
    (hx : ¬ ∃ k : ℤ, (k : ℝ) = x) :
    ‖charRealSubIcc M N x‖ ≤ 1 / (2 * distToInt x) := by
  rw [charRealSubIcc_eq_shift]
  have hunit : ‖charReal (((M + 1 : ℤ) : ℝ) * x)‖ = 1 := by
    dsimp [charReal]
    simpa using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (((M + 1 : ℤ) : ℝ) * x))
  calc
    ‖charReal (((M + 1 : ℤ) : ℝ) * x) *
        ∑ k ∈ Finset.range N, charReal ((k : ℝ) * x)‖
        ≤ 1 * ‖∑ k ∈ Finset.range N, charReal ((k : ℝ) * x)‖ := by
          rw [norm_mul, hunit]
    _ ≤ 1 / (2 * distToInt x) := by
          simpa using geomSum_exp_bound_far N hx

/-- **区间几何级数界**: `|Σ_{M<n≤M+N} e(nx)| ≤ min(N, 1/(2‖x‖))`
的两个组成部分. -/
theorem geomSum_exp_bound_Icc (M : ℤ) (N : ℕ) (x : ℝ) :
    ‖charRealSubIcc M N x‖ ≤ N ∧
      ((¬ ∃ k : ℤ, (k : ℝ) = x) →
        ‖charRealSubIcc M N x‖ ≤ 1 / (2 * distToInt x)) := by
  constructor
  · exact geomSum_exp_bound_Icc_trivial M N x
  · intro hx
    exact geomSum_exp_bound_Icc_far M N hx

end

end AnalyticNumberTheory.LargeSieve
