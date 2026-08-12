/-
! # AnalyticNumberTheory.Sieve.SelbergUpperBound

## Selberg 上界筛 (generic Selberg upper-bound sieve)

Selberg 筛法是陈氏定理中 Ω 上界估计的核心工具: 通过构造上界 Möbius 序列
(Λ² 权重), 把筛后计数分解为主项与误差项. 经典形式 (Halberstam--Richert
1974 Ch.3; Nathanson GTM 164 Ch.10; Liu 2022 §III):

  `S(A, P, z) ≤ X / G(z) + Σ |R_d|`,  G(z) = Σ_{d | P} g(d),

其中 `g(d) = ν(d)·∏_{p|d}(1−ν(p))⁻¹` 是 Selberg 项, 最优 Λ²-权重达到
主项 `mainSum = 1/G(z)`.

本模块提供:

1. **权重结构** — `SelbergWeights` (通用化自 chen 侧的陈氏版本) 与平凡
   存在性 `selberg_sieve_weights_exist`.
2. **Mathlib 对齐层** — 由 `SelbergWeights` 生成 `BoundingSieve.lambdaSquared`
   上界 Möbius 序列 (`selberg_lambda_is_upper_moebius`), 基本上界不等式
   (`omega_upper_bound_via_mathlib`), 主项对角化 (`mainSum_diag_via_mathlib`)
   与 Cauchy--Schwarz 最优性下界 (`mainSum_cauchy_schwarz_lower_bound`).
3. **最优 Selberg 权重** (本模块新增的核心) — 显式构造
   `optimalSelbergWeight` 使 `mainSum(Λ²w*) = (Σ g)⁻¹`
   (`optimalSelbergMainSum_eq`), 从而得到**无条件**的 Selberg 上界定理
   `selberg_upper_bound_optimal`.
4. **issue #6 目标陈述** — `UniformSelbergUpperBound`: 对一族 `BoundingSieve`
   的均匀 Selberg 上界 (量词顺序: `N₀` 先于 `∀ N`), 由最优权重定理直接
   成立; 陈氏常数 `3.9404·𝔖(N)·N/log²N` 形态还需 Mertens/奇异级数主项估计
   与加权 Pan 误差输入 (见 `WeightedPan` 与 chen 侧消费).

参考:
  - Selberg, A. (1947), Norske Vid. Selsk. Forh. Trondheim 19, 75-79
  - Halberstam & Richert, "Sieve Methods" (1974), Ch. 3
  - Nathanson, "Additive Number Theory: The Classical Bases" (1996), Ch. 10
  - Liu, Z. (2022), arXiv:2203.07871, §III
  - Mathlib `SelbergSieve.lean`: BoundingSieve, Λ² sieve, selbergTerms
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import AnalyticNumberTheory.Sieve.LinearSieve
import AnalyticNumberTheory.Sieve.SelbergIdentities

namespace AnalyticNumberTheory.Sieve

open Finset Real

open scoped Classical
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

/-! ## 1. Selberg 权重结构 -/

/-- Selberg 筛权重: 对筛积 `Q` 与水平 `z`,

1. `λ₁ = 1`;
2. `λ_d = 0` 当 `d > z` 或 `d ∤ Q`;
3. `|λ_d| ≤ 1`.

这是 chen 仓库陈氏版本 `SelbergWeights (N ε)` 的通用化: 陈氏实例取
`Q = selbergQ N ε` (不整除 `N` 的 `≤ z` 素数之积), `z = N^(1/4-ε/2)`. -/
structure SelbergWeights (Q z : ℕ) where
  /-- 权重函数 λ_d -/
  lambda : ℕ → ℝ
  /-- λ₁ = 1 -/
  lambda_one : lambda 1 = 1
  /-- λ_d = 0 当 d > z 或 d ∤ Q -/
  lambda_support : ∀ d : ℕ, d > z ∨ ¬ d ∣ Q → lambda d = 0
  /-- |λ_d| ≤ 1 -/
  lambda_bounded : ∀ d : ℕ, |lambda d| ≤ 1

/-- **平凡 Selberg 权重存在性**: `λ₁ = 1`、其余为 0 的权重是合法的
`SelbergWeights`, 其双重对角和 `Σ_{d₁,d₂} λ_{d₁}λ_{d₂}/φ([d₁,d₂]) = 1`
(只有 `d₁ = d₂ = 1` 一项). 这是陈氏 Lemma 3 (最优权重) 的平凡下界对照. -/
theorem selberg_sieve_weights_exist (Q z : ℕ) (hQ : Q ≠ 0) (hz : 1 ≤ z) :
    ∃ (SW : SelbergWeights Q z),
      (Q.divisors.sum (fun d₁ =>
        Q.divisors.sum (fun d₂ =>
          SW.lambda d₁ * SW.lambda d₂ / Nat.totient (Nat.lcm d₁ d₂)))) = 1 := by
  let SW : SelbergWeights Q z :=
    { lambda := fun d => if d = 1 then 1 else 0
      lambda_one := by simp
      lambda_support := by
        intro d hd
        by_cases hd1 : d = 1
        · subst d
          exfalso
          rcases hd with hlarge | hndvd
          · exact (not_lt_of_ge hz) hlarge
          · exact hndvd (Nat.one_dvd _)
        · simp [hd1]
      lambda_bounded := by
        intro d
        by_cases hd1 : d = 1 <;> simp [hd1] }
  refine ⟨SW, ?_⟩
  have h1mem : (1 : ℕ) ∈ Q.divisors := Nat.mem_divisors.mpr ⟨one_dvd Q, hQ⟩
  have hsum :
      (Q.divisors.sum (fun d₁ =>
        Q.divisors.sum (fun d₂ =>
          SW.lambda d₁ * SW.lambda d₂ / Nat.totient (Nat.lcm d₁ d₂)))) =
        (1 : ℝ) / Nat.totient 1 := by
    -- 内层: 只有 d₂ = 1 一项
    have hinner : ∀ d₁ : ℕ,
        (Q.divisors.sum (fun d₂ =>
          SW.lambda d₁ * SW.lambda d₂ / Nat.totient (Nat.lcm d₁ d₂))) =
          if d₁ = 1 then (1 : ℝ) / Nat.totient 1 else 0 := by
      intro d₁
      have hstep : (Q.divisors.sum (fun d₂ =>
            SW.lambda d₁ * SW.lambda d₂ / Nat.totient (Nat.lcm d₁ d₂))) =
          ∑ d₂ ∈ Q.divisors, if d₂ = 1 then
            SW.lambda d₁ * (1 : ℝ) / Nat.totient (Nat.lcm d₁ d₂) else 0 := by
        apply Finset.sum_congr rfl
        intro d₂ hd₂
        by_cases h : d₂ = 1
        · subst d₂
          simp [SW]
        · simp [SW, h]
      rw [hstep]
      rw [Finset.sum_ite_eq_of_mem' _ 1 _ h1mem]
      by_cases h : d₁ = 1
      · subst d₁
        simp [SW]
      · simp [SW, h]
    calc
      (Q.divisors.sum (fun d₁ =>
        Q.divisors.sum (fun d₂ =>
          SW.lambda d₁ * SW.lambda d₂ / Nat.totient (Nat.lcm d₁ d₂))))
          = ∑ d₁ ∈ Q.divisors, (if d₁ = 1 then (1 : ℝ) / Nat.totient 1 else 0) := by
            apply Finset.sum_congr rfl
            intro d₁ hd₁
            exact hinner d₁
      _ = (1 : ℝ) / Nat.totient 1 := by
            rw [Finset.sum_ite_eq_of_mem' _ 1 _ h1mem]
  simpa [Nat.totient_one] using hsum

/-! ## 2. Mathlib 对齐层 -/

/-- 给定 `SelbergWeights`, 构造 Mathlib 的 Λ² 权重:
`lambdaSquared weights d = Σ_{d₁|d} Σ_{d₂|d} [d = lcm(d₁,d₂)]·weights(d₁)·weights(d₂)`. -/
def selbergLambdaSquared {Q z : ℕ} (SW : SelbergWeights Q z) : ℕ → ℝ :=
  BoundingSieve.lambdaSquared SW.lambda

/-- **桥接定理 1**: Selberg 权重产生的 `lambdaSquared` 是上界 Möbius 序列. -/
theorem selberg_lambda_is_upper_moebius {Q z : ℕ} (SW : SelbergWeights Q z) :
    BoundingSieve.IsUpperMoebius (selbergLambdaSquared SW) := by
  exact BoundingSieve.upperMoebius_lambdaSquared SW.lambda SW.lambda_one

/-- **基本 Selberg 上界不等式** (Mathlib):
任意满足 `w 1 = 1` 的权重序列 `w` 生成的 Λ² 筛给出

  `siftedSum ≤ totalMass · mainSum(Λ²w) + errSum(Λ²w)`.

这是 Selberg 上界筛的骨架: 选择使 `mainSum` 最小的最优权重即得经典上界. -/
theorem omega_upper_bound_via_mathlib
    (S : BoundingSieve) (w : ℕ → ℝ) (hw : w 1 = 1) :
    S.siftedSum ≤ S.totalMass * S.mainSum (BoundingSieve.lambdaSquared w) +
      S.errSum (BoundingSieve.lambdaSquared w) := by
  exact BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius _
    (BoundingSieve.upperMoebius_lambdaSquared w hw)

/-- **主项对角化** (Mathlib): `mainSum(Λ²w)` 是特征值 `(selbergTerms l)⁻¹`
的二次型. -/
theorem mainSum_diag_via_mathlib
    (S : BoundingSieve) (w : ℕ → ℝ) :
    S.mainSum (BoundingSieve.lambdaSquared w) =
      ∑ l ∈ S.prodPrimes.divisors, (S.selbergTerms l)⁻¹ *
        (∑ d ∈ S.prodPrimes.divisors,
          if l ∣ d then S.nu d * w d else 0) ^ 2 := by
  exact S.mainSum_lambdaSquared_eq_sum_mul_sum_sq w

/-- **最优性下界** (Cauchy--Schwarz / Titu): 对任意 `w` 满足 `w 1 = 1`,

  `mainSum(Λ²w) ≥ (Σ_{l | P} selbergTerms l)⁻¹`.

等号恰由最优 Selberg 权重达到 (见下节 `optimalSelbergMainSum_eq`). -/
theorem mainSum_cauchy_schwarz_lower_bound
    (S : BoundingSieve) (w : ℕ → ℝ) (hw : w 1 = 1) :
    (S.prodPrimes.divisors.sum (fun l => S.selbergTerms l))⁻¹ ≤
      S.mainSum (BoundingSieve.lambdaSquared w) := by
  -- Helper: Σ_{l ∈ d.divisors} (μ l : ℝ) = [d = 1]
  -- This follows from (ζ * μ)(d) = 1(d) via Möbius inversion
  have hMoebiusSum : ∀ d ∈ S.prodPrimes.divisors,
      ∑ l ∈ d.divisors, (μ l : ℝ) = if d = 1 then (1 : ℝ) else 0 := by
    intro d hd
    have h := ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℝ)
    have hkey : (ζ * (μ : ArithmeticFunction ℝ)) d = (1 : ArithmeticFunction ℝ) d := by rw [h]
    rw [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply] at hkey
    simp only [ArithmeticFunction.intCoe_apply] at hkey
    exact hkey
  -- Möbius inversion: Σ_l (μ l : ℝ) * x_l = 1
  -- where x_l = Σ_{d ∈ D} [l|d] ν(d) w(d)
  have hMoebiusInv : ∑ l ∈ S.prodPrimes.divisors,
      (μ l : ℝ) * (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0) = 1 := by
    calc ∑ l ∈ S.prodPrimes.divisors,
          (μ l : ℝ) * (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0)
        = ∑ l ∈ S.prodPrimes.divisors,
            ∑ d ∈ S.prodPrimes.divisors,
              (μ l : ℝ) * (if l ∣ d then S.nu d * w d else 0) := by simp_rw [mul_sum]
      _ = ∑ d ∈ S.prodPrimes.divisors,
            ∑ l ∈ S.prodPrimes.divisors,
              (μ l : ℝ) * (if l ∣ d then S.nu d * w d else 0) := by rw [sum_comm]
      _ = ∑ d ∈ S.prodPrimes.divisors,
            S.nu d * w d * (∑ l ∈ d.divisors, (μ l : ℝ)) := by
        refine sum_congr rfl fun d hd => ?_
        have hdvd : d ∣ S.prodPrimes := (Nat.mem_divisors.mp hd).1
        simp_rw [mul_ite, mul_zero]
        rw [← sum_filter, Nat.divisors_filter_dvd_of_dvd S.prodPrimes_ne_zero hdvd, mul_sum]
        exact sum_congr rfl (fun l _ => mul_comm _ _)
      _ = ∑ d ∈ S.prodPrimes.divisors,
            S.nu d * w d * (if d = 1 then (1 : ℝ) else 0) := by
        refine sum_congr rfl fun d hd => ?_
        rw [hMoebiusSum d hd]
      _ = S.nu 1 * w 1 := by
        have h1mem : (1 : ℕ) ∈ S.prodPrimes.divisors :=
          Nat.mem_divisors.mpr ⟨one_dvd S.prodPrimes, S.prodPrimes_ne_zero⟩
        simp_rw [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq_of_mem' _ _ _ h1mem]
      _ = 1 := by
        have h_nu1 : S.nu 1 = 1 := S.nu_mult.map_one
        rw [h_nu1, hw]
        norm_num
  -- Titu's lemma (Sedrakyan's lemma / Engel form of Cauchy-Schwarz)
  -- Applied with f_l = (μ l : ℝ) * x_l, g_l = selbergTerms l * (μ l : ℝ)²
  have hTitu :
      (∑ l ∈ S.prodPrimes.divisors,
        (μ l : ℝ) * (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0)) ^ 2 /
      ∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l * (μ l : ℝ) ^ 2 ≤
      ∑ l ∈ S.prodPrimes.divisors,
        ((μ l : ℝ) * (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0)) ^ 2 /
        (S.selbergTerms l * (μ l : ℝ) ^ 2) := by
    apply sq_sum_div_le_sum_sq_div
    intro l hl
    have hsq := S.squarefree_of_mem_divisors_prodPrimes hl
    have hpos := S.selbergTerms_pos ((Nat.mem_divisors.mp hl).1)
    have hμsq : (μ l : ℝ) ^ 2 = 1 := by exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    rw [hμsq, mul_one]
    exact hpos
  -- Simplify denominator: Σ selbergTerms l * μ(l)² = Σ selbergTerms l
  -- (since all l | P are squarefree, μ(l)² = 1)
  have hDenom : ∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l * (μ l : ℝ) ^ 2 =
      ∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l := by
    refine sum_congr rfl fun l hl => ?_
    have hsq := S.squarefree_of_mem_divisors_prodPrimes hl
    have hμsq : (μ l : ℝ) ^ 2 = 1 := by exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    rw [hμsq, mul_one]
  -- Simplify RHS: Σ ((μ l) * x_l)² / (selbergTerms l * μ(l)²) = Σ selbergTerms(l)⁻¹ * x_l²
  have hRHS : ∑ l ∈ S.prodPrimes.divisors,
        ((μ l : ℝ) * (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0)) ^ 2 /
        (S.selbergTerms l * (μ l : ℝ) ^ 2) =
      ∑ l ∈ S.prodPrimes.divisors,
        (S.selbergTerms l)⁻¹ *
        (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0) ^ 2 := by
    refine sum_congr rfl fun l hl => ?_
    have hsq := S.squarefree_of_mem_divisors_prodPrimes hl
    have hμsq : (μ l : ℝ) ^ 2 = 1 := by exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    rw [hμsq, mul_one, mul_pow, hμsq, one_mul, div_eq_inv_mul]
  -- Diagonalization (Mathlib: mainSum_lambdaSquared_eq_sum_mul_sum_sq)
  have h_diag : S.mainSum (BoundingSieve.lambdaSquared w) =
      ∑ l ∈ S.prodPrimes.divisors,
        (S.selbergTerms l)⁻¹ *
        (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0) ^ 2 :=
    S.mainSum_lambdaSquared_eq_sum_mul_sum_sq w
  -- Chain everything together
  rw [hMoebiusInv, hDenom] at hTitu
  simp only [one_pow] at hTitu
  rw [hRHS] at hTitu
  rw [one_div] at hTitu
  rw [h_diag]
  exact hTitu

/-! ## 3. 最优 Selberg 权重 -/

/-- Selberg 最优主项: `(Σ_{l | P} selbergTerms l)⁻¹`. -/
noncomputable def selbergMainTerm (S : BoundingSieve) : ℝ :=
  (∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l)⁻¹

/-- 最优对角值 `x*_l = g(l)·μ(l)·(Σg)⁻¹`: 对角化二次型
`Σ_l (g(l))⁻¹·x_l²` 在约束 `w(1)=1` 下的最小化取值. -/
noncomputable def optimalSelbergX (S : BoundingSieve) (l : ℕ) : ℝ :=
  S.selbergTerms l * (μ l : ℝ) * selbergMainTerm S

/-- **最优 Selberg Λ²-权重**: `optimalSelbergX` 在筛积 `prodPrimes` 的
除数格上的超集 Möbius 逆变换, 再除以密度 `ν`:

  `w*(d) = ν(d)⁻¹ · Σ_{e : d|e|P} μ(e/d)·x*_e`.

由 `optimalSelbergMainSum_eq`, `mainSum(Λ²w*) = (Σ g)⁻¹`, 恰为
Cauchy--Schwarz 下界 `mainSum_cauchy_schwarz_lower_bound` 的等号情形. -/
noncomputable def optimalSelbergWeight (S : BoundingSieve) : ℕ → ℝ :=
  fun d =>
    if _hd : d ∣ S.prodPrimes then
      (∑ e ∈ S.prodPrimes.divisors,
        if d ∣ e then (μ (e / d) : ℝ) * optimalSelbergX S e else 0) / S.nu d
    else 0

/-- 标准 Möbius 和: `Σ_{d | n} μ(d) = [n = 1]`. -/
private lemma sum_moebius_eq_one {n : ℕ} :
    (∑ d ∈ n.divisors, (μ d : ℝ)) = if n = 1 then (1 : ℝ) else 0 := by
  have h := ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℝ)
  have hkey : (ζ * (μ : ArithmeticFunction ℝ)) n = (1 : ArithmeticFunction ℝ) n := by rw [h]
  rw [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply] at hkey
  simpa [ArithmeticFunction.intCoe_apply, mul_comm] using hkey

/-- `l | d ⟺ e/d | e/l` (对 `d | e`, `l | e`): 把"被 `l` 整除"翻译成
"整除 `e/l`"的商形式. 用于受限 Möbius 和的换元. -/
private lemma dvd_iff_div_dvd {e l d : ℕ} (he : e ≠ 0) (hd : d ∣ e) (hl : l ∣ e) :
    l ∣ d ↔ e / d ∣ e / l := by
  constructor
  · intro hld
    rcases hld with ⟨k, rfl⟩
    have hl0 : 0 < l := Nat.pos_of_dvd_of_pos hl (Nat.pos_of_ne_zero he)
    have hkl : k ∣ e / l := by
      have heq : e = l * (e / l) := by
        rw [mul_comm, Nat.div_mul_cancel hl]
      rw [heq] at hd
      exact (Nat.mul_dvd_mul_iff_left hl0).mp hd
    have hq : e / (l * k) = (e / l) / k := (Nat.div_div_eq_div_mul e l k).symm
    rw [hq]
    exact Nat.div_dvd_of_dvd hkl
  · intro hdl
    rcases hdl with ⟨j, hj⟩
    have heq1 : e = l * (e / l) := by
      rw [mul_comm, Nat.div_mul_cancel hl]
    have heq2 : d * (e / d) = e := by
      rw [mul_comm, Nat.div_mul_cancel hd]
    have hdq : 0 < e / d :=
      Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd hd) (Nat.pos_of_ne_zero he)
    have hmain : d * (e / d) = l * j * (e / d) := by
      calc
        d * (e / d) = e := heq2
        _ = l * (e / l) := heq1
        _ = l * (j * (e / d)) := by
          rw [hj]
          ring
        _ = l * j * (e / d) := by ring
    refine ⟨j, ?_⟩
    exact Nat.mul_right_cancel hdq hmain

/-- 受限 Möbius 和: 对 `l | e`, `Σ_{d | e, l | d} μ(e/d) = [e = l]`. -/
private lemma sum_moebius_quotient_of_dvd {e l : ℕ} (he : e ≠ 0) (hle : l ∣ e) :
    (∑ d ∈ e.divisors, if l ∣ d then (μ (e / d) : ℝ) else 0) =
      if e = l then (1 : ℝ) else 0 := by
  -- 重排 d ↦ e/d: 在商形式下 `[l|d]` 变成 `[e/d | e/l]`
  have hbij :
      (∑ d ∈ e.divisors, if l ∣ d then (μ (e / d) : ℝ) else 0) =
        ∑ d ∈ e.divisors, if d ∣ e / l then (μ d : ℝ) else 0 := by
    refine Finset.sum_bij (fun d _ => e / d) ?_ ?_ ?_ ?_
    · intro d hd
      have hdvd : d ∣ e := (Nat.mem_divisors.mp hd).1
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, he⟩
    · intro a ha b hb hab
      have havd : a ∣ e := (Nat.mem_divisors.mp ha).1
      have hbvd : b ∣ e := (Nat.mem_divisors.mp hb).1
      calc
        a = e / (e / a) := (Nat.div_div_self havd he).symm
        _ = e / (e / b) := by rw [hab]
        _ = b := Nat.div_div_self hbvd he
    · intro d hd
      have hdvd : d ∣ e := (Nat.mem_divisors.mp hd).1
      refine ⟨e / d, ?_, ?_⟩
      · exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, he⟩
      · exact Nat.div_div_self hdvd he
    · intro d hd
      have hdvd : d ∣ e := (Nat.mem_divisors.mp hd).1
      by_cases hld : l ∣ d
      · have hdld : e / d ∣ e / l := (dvd_iff_div_dvd he hdvd hle).mp hld
        simp [hld, hdld]
      · have hndld : ¬ e / d ∣ e / l := by
          intro h
          apply hld
          exact (dvd_iff_div_dvd he hdvd hle).mpr h
        simp [hld, hndld]
  rw [hbij]
  -- 现在 `Σ_{d | e, d | e/l} μ(d)`; 由于 `e/l | e`, 该集合恰为 `(e/l).divisors`
  have hfilter : e.divisors.filter (fun d => d ∣ e / l) = (e / l).divisors :=
    Nat.divisors_filter_dvd_of_dvd he (Nat.div_dvd_of_dvd hle)
  rw [← Finset.sum_filter]
  rw [hfilter]
  rw [sum_moebius_eq_one]
  by_cases hel : e = l
  · have hl0 : 0 < l := Nat.pos_of_dvd_of_pos hle (Nat.pos_of_ne_zero he)
    simp [hel]
    exact Nat.div_self hl0
  · have hdiv_ne : e / l ≠ 1 := by
      intro h
      apply hel
      calc
        e = l * (e / l) := by rw [mul_comm, Nat.div_mul_cancel hle]
        _ = l * 1 := by rw [h]
        _ = l := by rw [mul_one]
    simp [hdiv_ne, hel]

/-- **最优权重的归一化**: `w*(1) = 1`. -/
theorem optimalSelbergWeight_one (S : BoundingSieve) :
    optimalSelbergWeight S 1 = 1 := by
  unfold optimalSelbergWeight
  rw [dif_pos (one_dvd S.prodPrimes)]
  -- 分子: Σ_{e | P} μ(e)·x*_e = (Σg)⁻¹·Σ_e g(e)·μ(e)² = (Σg)⁻¹·Σg = 1
  have hnum : (∑ e ∈ S.prodPrimes.divisors,
        (μ (e / 1) : ℝ) * optimalSelbergX S e) = 1 := by
    have hstep1 : (∑ e ∈ S.prodPrimes.divisors,
        (μ (e / 1) : ℝ) * optimalSelbergX S e) =
        selbergMainTerm S * (∑ e ∈ S.prodPrimes.divisors, S.selbergTerms e) := by
      -- e / 1 = e, 且 μ(e)·x*_e = μ(e)·g(e)·μ(e)·T = T·g(e)·μ(e)² = T·g(e)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      have hsq := S.squarefree_of_mem_divisors_prodPrimes he
      have hμsq : (μ e : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
      unfold optimalSelbergX
      simp only [Nat.div_one]
      ring_nf
      rw [hμsq]
      ring
    rw [hstep1]
    unfold selbergMainTerm
    have hsum_ne : (∑ e ∈ S.prodPrimes.divisors, S.selbergTerms e) ≠ 0 := by
      have h1mem : (1 : ℕ) ∈ S.prodPrimes.divisors :=
        Nat.mem_divisors.mpr ⟨one_dvd S.prodPrimes, S.prodPrimes_ne_zero⟩
      have hpos1 : 0 < S.selbergTerms 1 := by
        rw [BoundingSieve.selbergTerms_apply]
        have hν1 : S.nu 1 = 1 := S.nu_mult.map_one
        simp [hν1]
      exact ne_of_gt (Finset.sum_pos
        (fun e he => S.selbergTerms_pos ((Nat.mem_divisors.mp he).1)) ⟨1, h1mem⟩)
    field_simp [hsum_ne]
  -- 分母 ν(1) = 1
  have hν1 : S.nu 1 = 1 := S.nu_mult.map_one
  rw [hν1]
  have hif : (∑ e ∈ S.prodPrimes.divisors,
        if (1 : ℕ) ∣ e then (μ (e / 1) : ℝ) * optimalSelbergX S e else 0) =
      ∑ e ∈ S.prodPrimes.divisors, (μ (e / 1) : ℝ) * optimalSelbergX S e := by
    apply Finset.sum_congr rfl
    intro e he
    rw [if_pos (one_dvd e)]
  rw [hif, hnum]
  norm_num

/-- **对角值识别**: 最优权重在 `l` 处的 `ν`-加权和恰为 `x*_l`:

  `Σ_{d : l|d|P} ν(d)·w*(d) = x*_l`.

这是超集 Möbius 逆变换 `w* = ν⁻¹·(y*)` 的精确依据, 其中
`y*(d) = Σ_{e : d|e|P} μ(e/d)·x*_e`. -/
theorem optimalSelbergX_eq_sum_nu_mul_weight (S : BoundingSieve) (l : ℕ)
    (hl : l ∣ S.prodPrimes) :
    optimalSelbergX S l =
      ∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * optimalSelbergWeight S d else 0 := by
  -- 对 d | P, ν(d)·w*(d) = y*(d) := Σ_{e : d|e|P} μ(e/d)·x*_e
  have hd_def : ∀ d : ℕ, d ∈ S.prodPrimes.divisors →
      S.nu d * optimalSelbergWeight S d =
        ∑ e ∈ S.prodPrimes.divisors, if d ∣ e then (μ (e / d) : ℝ) * optimalSelbergX S e else 0 := by
    intro d hd
    have hdvd : d ∣ S.prodPrimes := (Nat.mem_divisors.mp hd).1
    have hν : S.nu d ≠ 0 := S.nu_ne_zero hdvd
    unfold optimalSelbergWeight
    rw [dif_pos hdvd]
    field_simp [hν]
  -- 交换求和序: Σ_d [l|d]·Σ_e [d|e]·μ(e/d)·x*_e = Σ_e x*_e·(Σ_{d: l|d|e} μ(e/d))
  have hswap :
      (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then
          (∑ e ∈ S.prodPrimes.divisors, if d ∣ e then (μ (e / d) : ℝ) * optimalSelbergX S e else 0)
        else 0) =
        ∑ e ∈ S.prodPrimes.divisors, optimalSelbergX S e *
          (∑ d ∈ S.prodPrimes.divisors,
            if l ∣ d then (if d ∣ e then (μ (e / d) : ℝ) else 0) else 0) := by
    -- 先把内层和写成乘法形式再换序
    calc
      (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then
          (∑ e ∈ S.prodPrimes.divisors, if d ∣ e then (μ (e / d) : ℝ) * optimalSelbergX S e else 0)
        else 0)
          = ∑ d ∈ S.prodPrimes.divisors,
              ∑ e ∈ S.prodPrimes.divisors,
                if l ∣ d then (if d ∣ e then (μ (e / d) : ℝ) * optimalSelbergX S e else 0) else 0 := by
              apply Finset.sum_congr rfl
              intro d hd
              by_cases hld : l ∣ d
              · simp [hld]
              · simp [hld]
      _ = ∑ e ∈ S.prodPrimes.divisors,
              ∑ d ∈ S.prodPrimes.divisors,
                if l ∣ d then (if d ∣ e then (μ (e / d) : ℝ) * optimalSelbergX S e else 0) else 0 := by
              rw [Finset.sum_comm]
      _ = ∑ e ∈ S.prodPrimes.divisors, optimalSelbergX S e *
              (∑ d ∈ S.prodPrimes.divisors,
                if l ∣ d then (if d ∣ e then (μ (e / d) : ℝ) else 0) else 0) := by
              apply Finset.sum_congr rfl
              intro e he
              -- 内层: Σ_d [l|d]·[d|e]·μ(e/d)·x*_e = x*_e · Σ_d [l|d]·[d|e]·μ(e/d)
              have hinner : (∑ d ∈ S.prodPrimes.divisors,
                    if l ∣ d then (if d ∣ e then (μ (e / d) : ℝ) * optimalSelbergX S e else 0) else 0) =
                  optimalSelbergX S e *
                    (∑ d ∈ S.prodPrimes.divisors,
                      if l ∣ d then (if d ∣ e then (μ (e / d) : ℝ) else 0) else 0) := by
                rw [mul_comm]
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro d hd
                by_cases hld : l ∣ d
                · by_cases hde : d ∣ e
                  · simp [hld, hde]
                  · simp [hld, hde]
                · simp [hld]
              rw [hinner]
  -- 内层和 (对固定 e): Σ_{d: l|d|e} μ(e/d) = [e = l]
  have hinner_delta : ∀ e : ℕ, e ∈ S.prodPrimes.divisors →
      (∑ d ∈ S.prodPrimes.divisors,
        if l ∣ d then (if d ∣ e then (μ (e / d) : ℝ) else 0) else 0) =
        if e = l then (1 : ℝ) else 0 := by
    intro e he
    have hdvd_e : e ∣ S.prodPrimes := (Nat.mem_divisors.mp he).1
    have he0 : e ≠ 0 := Nat.ne_of_gt (Nat.pos_of_dvd_of_pos hdvd_e (Nat.pos_of_ne_zero S.prodPrimes_ne_zero))
    have hrestrict :
        (∑ d ∈ S.prodPrimes.divisors,
          if l ∣ d then (if d ∣ e then (μ (e / d) : ℝ) else 0) else 0) =
          ∑ d ∈ e.divisors, if l ∣ d then (μ (e / d) : ℝ) else 0 := by
      -- 把双重条件压成单条件再换到 e.divisors 上
      have hfilt : S.prodPrimes.divisors.filter (fun d => l ∣ d ∧ d ∣ e) =
          e.divisors.filter (fun d => l ∣ d) := by
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors]
        constructor
        · intro h
          exact ⟨⟨h.2.2, he0⟩, h.2.1⟩
        · intro h
          exact ⟨⟨h.1.1.trans hdvd_e, S.prodPrimes_ne_zero⟩, h.2, h.1.1⟩
      calc
        (∑ d ∈ S.prodPrimes.divisors,
          if l ∣ d then (if d ∣ e then (μ (e / d) : ℝ) else 0) else 0)
            = ∑ d ∈ S.prodPrimes.divisors, if l ∣ d ∧ d ∣ e then (μ (e / d) : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro d hd
              by_cases hld : l ∣ d <;> by_cases hde : d ∣ e <;> simp [hld, hde]
        _ = ∑ d ∈ (S.prodPrimes.divisors.filter (fun d => l ∣ d ∧ d ∣ e)), (μ (e / d) : ℝ) := by
              rw [← Finset.sum_filter]
        _ = ∑ d ∈ (e.divisors.filter (fun d => l ∣ d)), (μ (e / d) : ℝ) := by
              rw [hfilt]
        _ = ∑ d ∈ e.divisors, if l ∣ d then (μ (e / d) : ℝ) else 0 := by
              rw [Finset.sum_filter]
    rw [hrestrict]
    by_cases hle : l ∣ e
    · rw [sum_moebius_quotient_of_dvd he0 hle]
    · have hne : e ≠ l := by intro hel; apply hle; rw [hel]
      -- l ∤ e 时内层和为空
      have hsum0 : (∑ d ∈ e.divisors, if l ∣ d then (μ (e / d) : ℝ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro d hd
        by_cases hld : l ∣ d
        · exfalso
          apply hle
          exact hld.trans (Nat.mem_divisors.mp hd).1
        · simp [hld]
      rw [hsum0]
      simp [hne]
  -- 组装
  calc
    optimalSelbergX S l
        = ∑ e ∈ S.prodPrimes.divisors, optimalSelbergX S e *
            (if e = l then (1 : ℝ) else 0) := by
          have hlm : l ∈ S.prodPrimes.divisors :=
            Nat.mem_divisors.mpr ⟨hl, S.prodPrimes_ne_zero⟩
          simp_rw [mul_ite, mul_one, mul_zero]
          rw [← Finset.sum_ite_eq_of_mem' S.prodPrimes.divisors l (fun e => optimalSelbergX S e) hlm]
    _ = ∑ e ∈ S.prodPrimes.divisors, optimalSelbergX S e *
          (∑ d ∈ S.prodPrimes.divisors,
            if l ∣ d then (if d ∣ e then (μ (e / d) : ℝ) else 0) else 0) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [← hinner_delta e he]
    _ = ∑ d ∈ S.prodPrimes.divisors, if l ∣ d then
            (∑ e ∈ S.prodPrimes.divisors, if d ∣ e then (μ (e / d) : ℝ) * optimalSelbergX S e else 0)
          else 0 := hswap.symm
    _ = ∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * optimalSelbergWeight S d else 0 := by
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hld : l ∣ d
          · rw [← hd_def d hd]
          · simp [hld]

/-- **最优主项等式**: `mainSum(Λ²w*) = (Σ_{l | P} selbergTerms l)⁻¹`,
即 Cauchy--Schwarz 下界 `mainSum_cauchy_schwarz_lower_bound` 的等号情形. -/
theorem optimalSelbergMainSum_eq (S : BoundingSieve) :
    S.mainSum (BoundingSieve.lambdaSquared (optimalSelbergWeight S)) = selbergMainTerm S := by
  rw [mainSum_diag_via_mathlib]
  -- 内层和 = x*_l
  have hx : ∀ l ∈ S.prodPrimes.divisors,
      (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * optimalSelbergWeight S d else 0) =
        optimalSelbergX S l := by
    intro l hl
    exact (optimalSelbergX_eq_sum_nu_mul_weight S l ((Nat.mem_divisors.mp hl).1)).symm
  have hsum1 : (∑ l ∈ S.prodPrimes.divisors,
        (S.selbergTerms l)⁻¹ *
          (∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * optimalSelbergWeight S d else 0) ^ 2) =
      ∑ l ∈ S.prodPrimes.divisors, (S.selbergTerms l)⁻¹ * (optimalSelbergX S l) ^ 2 := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [← hx l hl]
  rw [hsum1]
  -- 展开 x*_l = g(l)·μ(l)·T: 每项 = T²·g(l)
  have hsum2 : (∑ l ∈ S.prodPrimes.divisors,
        (S.selbergTerms l)⁻¹ * (optimalSelbergX S l) ^ 2) =
      (selbergMainTerm S) ^ 2 * (∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    have hg : S.selbergTerms l ≠ 0 := (S.selbergTerms_pos ((Nat.mem_divisors.mp hl).1)).ne'
    have hsq := S.squarefree_of_mem_divisors_prodPrimes hl
    have hμsq : ((μ l : ℝ) ^ 2) = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    unfold optimalSelbergX
    have hx2 : (S.selbergTerms l * (μ l : ℝ) * selbergMainTerm S) ^ 2 =
        (S.selbergTerms l) ^ 2 * ((μ l : ℝ) ^ 2) * (selbergMainTerm S) ^ 2 := by ring
    rw [hx2, hμsq]
    field_simp [hg]
  rw [hsum2]
  -- T²·Σg = T
  unfold selbergMainTerm
  have hsum_ne : (∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l) ≠ 0 := by
    have h1mem : (1 : ℕ) ∈ S.prodPrimes.divisors :=
      Nat.mem_divisors.mpr ⟨one_dvd S.prodPrimes, S.prodPrimes_ne_zero⟩
    have hpos1 : 0 < S.selbergTerms 1 := by
      rw [BoundingSieve.selbergTerms_apply]
      have hν1 : S.nu 1 = 1 := S.nu_mult.map_one
      simp [hν1]
    exact ne_of_gt (Finset.sum_pos
      (fun l hl => S.selbergTerms_pos ((Nat.mem_divisors.mp hl).1)) ⟨1, h1mem⟩)
  field_simp [hsum_ne]

/-- **Selberg 上界定理 (无条件)**: 最优 Λ²-权重使主项最小化,

  `siftedSum ≤ totalMass · (Σ_{l | P} selbergTerms l)⁻¹ + errSum(Λ²w*)`.

这是经典 Selberg 上界筛 `S ≤ X/G(z) + R` 的精确有限形式 (Halberstam--
Richert 1974 Ch.3); 陈氏应用中 `(Σg)⁻¹ ≈ 8𝔖(N)/log N` 与 `errSum ≪
N/log^A N` 分别由 Mertens/奇异级数主项估计和加权 Pan 输入给出. -/
theorem selberg_upper_bound_optimal (S : BoundingSieve) :
    ∃ w : ℕ → ℝ, w 1 = 1 ∧
      S.siftedSum ≤
        S.totalMass * (∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l)⁻¹ +
          S.errSum (BoundingSieve.lambdaSquared w) := by
  refine ⟨optimalSelbergWeight S, optimalSelbergWeight_one S, ?_⟩
  have h := omega_upper_bound_via_mathlib S (optimalSelbergWeight S) (optimalSelbergWeight_one S)
  rw [optimalSelbergMainSum_eq S] at h
  simpa [selbergMainTerm] using h

/-- **Selberg 主项的筛积形式**: 对任意 `BoundingSieve`,

  `(Σ_{d | P} selbergTerms d)⁻¹ = ∏_{p | P} (1 − ν(p))`.

由 `selbergSum_eq_prod_inv` (`Σg = ∏(1−ν(p))⁻¹`) 取逆得到. 对经典
`SieveProblem`, 右端即 `sieveProduct` (见 `selbergMainTerm_eq_sieveProduct`). -/
theorem selbergMainTerm_eq_prod_one_sub_nu (S : BoundingSieve) :
    (∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l)⁻¹ =
      ∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p) := by
  calc
    (∑ l ∈ S.prodPrimes.divisors, S.selbergTerms l)⁻¹
        = (∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p)⁻¹)⁻¹ := by
            rw [selbergSum_eq_prod_inv]
    _ = ∏ p ∈ S.prodPrimes.primeFactors, ((1 - S.nu p)⁻¹)⁻¹ := by
            rw [← Finset.prod_inv_distrib]
    _ = ∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p) := by
            apply Finset.prod_congr rfl
            intro p hp
            have hp_p : p.Prime := Nat.prime_of_mem_primeFactors hp
            have hp_dvd : p ∣ S.prodPrimes := Nat.dvd_of_mem_primeFactors hp
            have hne : (1 - S.nu p) ≠ 0 := by
              linarith [S.nu_lt_one_of_prime p hp_p hp_dvd]
            exact inv_inv (1 - S.nu p)

/-- **经典 `SieveProblem` 下的主项筛积形式**:
`(Σ_{d | P} selbergTerms d)⁻¹ = sieveProduct`. -/
theorem selbergMainTerm_eq_sieveProduct (SP : SieveProblem) :
    (∑ l ∈ SP.prodPrimes.divisors, SP.selbergTerms l)⁻¹ = sieveProduct SP := by
  rw [selbergMainTerm_eq_prod_one_sub_nu SP.toBoundingSieve, sieveProduct_eq_prod_one_sub_nu SP]

/-- **Selberg 上界的筛积形式**: 经典 `SieveProblem` 下最优 Λ²-权重给出

  `siftedSum ≤ totalMass · V(z) + errSum(Λ²w*)`,  V(z) = sieveProduct.

这是陈氏 Ω 上界消费 (chen sub-issue #7) 需要的精确主项形状:
`(Σg)⁻¹ = V(z)`, 而 `V(z)` 由 Mertens/奇异级数接缝控制. -/
theorem selberg_upper_bound_sieveProduct (SP : SieveProblem) :
    ∃ w : ℕ → ℝ, w 1 = 1 ∧
      SP.siftedSum ≤ SP.totalMass * sieveProduct SP +
        SP.errSum (BoundingSieve.lambdaSquared w) := by
  obtain ⟨w, hw1, hbound⟩ := selberg_upper_bound_optimal SP.toBoundingSieve
  refine ⟨w, hw1, ?_⟩
  rwa [selbergMainTerm_eq_sieveProduct SP] at hbound

/-! ## 4. issue #6 目标陈述 -/

/-- **一致 Selberg 上界 (issue #6 目标陈述)**.

经典形式 (Halberstam--Richert Ch.3, 陈氏应用): 对充分大的偶数 `N`,

  `S(A,z) ≤ X/G(z) + Σ |R_d|`,  G(z) = Σ_{d | P} g(d).

本仓库的有限翻译: 存在 `N₀`, 对每个偶数 `N ≥ N₀` 都存在一个满足
`w 1 = 1` 的权重序列, 使

  `siftedSum ≤ totalMass · (Σ_{d | P} g(d))⁻¹ + errSum(Λ²w)`.

量词顺序是判定标准: `N₀` 先于 `∀ N`. 由最优权重定理
`selberg_upper_bound_optimal`, 该目标对任意 `BoundingSieve` 族**无条件**
成立 (定理 `uniformSelbergUpperBound`). 陈氏 `3.9404·𝔖(N)·N/log²N` 常数
形态还需两个解析输入: (1) Mertens/奇异级数主项估计
`(Σg)⁻¹ ≈ 8𝔖(N)/log N`; (2) 加权 Pan 误差 `errSum = O(N/log^A N)`
(见 `WeightedPan` 模块与 chen 仓库消费). -/
def UniformSelbergUpperBound (SP : ℕ → BoundingSieve) : Prop :=
  ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ w : ℕ → ℝ,
        w 1 = 1 ∧
          (SP N).siftedSum ≤
            (SP N).totalMass *
                (∑ l ∈ (SP N).prodPrimes.divisors, (SP N).selbergTerms l)⁻¹ +
              (SP N).errSum (BoundingSieve.lambdaSquared w)

/-- 最优 Selberg 权重对任意筛族给出一致 Selberg 上界 (issue #6 结构层). -/
theorem uniformSelbergUpperBound (SP : ℕ → BoundingSieve) :
    UniformSelbergUpperBound SP := by
  refine ⟨0, ?_⟩
  intro N hN₀ hEven
  exact selberg_upper_bound_optimal (SP N)

/-! ## 5. 陈氏数值常数 -/

/-- 8 × 0.49254 = 3.94032: 陈氏 Ω 上界主项系数的代数来源 (Chen 1973 (28) 式
的数值积分 `0.49254` 与 Selberg 主项对角化系数 `8`). -/
theorem coefficient_product : (8 : ℝ) * 0.49254 = 3.94032 := by
  norm_num

end AnalyticNumberTheory.Sieve
