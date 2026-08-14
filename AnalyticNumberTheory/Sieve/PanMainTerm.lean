/-
! # AnalyticNumberTheory.Sieve.PanMainTerm

## T3: li 主项部分的加权界 — 归约链 (ant #15 装配链, 分支 research/pan-main-term)

`PanMeanValueUniform` 的装配把 a-吸收后的对象拆成 type I (`apV1`), type II
(`apV3`) 与 **主项** (`li` 部分) 三块 (Liu 2022 §III; Halberstam--Richert
1974 Ch.10). 本文件推进第三块: `PanMainTermBound` (见
`PanMeanValueBody.lean` §4) 的归约链.

## 数学本质

主项对象 (去 max 前) 是 `Σ_{(a,q)=1, a ≤ X} f(a)·li(⌊y/a⌋)/φ(q)`, 其中
`logarithmicIntegral x = x/log x` (工作定义, `BombieriVinogradov.lean`).
对 `|f| ≤ 1`:

```text
|Σ_a f(a)·li(⌊y/a⌋)/φ(q)| ≤ Σ_{a ≤ X} |li(⌊y/a⌋)| / φ(q)
  ≤ (max_{y ≤ x} Σ_{a ≤ X} |li(⌊y/a⌋)|) / φ(q)
```

所以带权重和

```text
Σ_{q ≤ Q} μ²(q)·3^{ω(q)}·max_y max_l |Σ_a f(a)·li(⌊y/a⌋)/φ(q)|
  ≤ max_{y ≤ x} Σ_{a ≤ X} |li(⌊y/a⌋)| · Σ_{q ≤ Q} μ²(q)·3^{ω(q)}/φ(q)
```

本文件的归约定理 `PanMainTermBound.of_sieveBound` 把 `PanMainTermBound`
精确归约到辅助台阶 `PanMainTermSieveBound` (上述两个因子的乘积的最终
`C·xX/log^A(xX)` 界), 全部有限代数 (三角不等式, |f| ≤ 1, l-max/y-max 归约,
权重非负, q = 0 零权重) 在此证明 — 与 T1 的
`PanTypeICharacterMeanValue.of_sieveBound` 同构.

## 两个因子的初等估计 (本文件 §3--§4 全证)

- **y,a 因子** (§3): `|li(m)| ≤ m/log 2` (所有自然数 m), 从而
  `Σ_{a ≤ X} |li(⌊y/a⌋)| ≤ (y/log 2)·(1 + log X)`,
  `max_{y ≤ x} ≤ (x/log 2)·(1 + log X)` (调和级数 + floor ≤ 值).
- **q 因子** (§4): 对平方自由 q 有 `μ²(q)·3^{ω(q)}/φ(q) = ∏_{p|q} 3/(p-1)`
  (`goldbachNu_squarefree_eq_inv_totient`), 子集展开
  `Σ_{q ≤ Q, sqfree} ∏_{p|q} c_p ≤ ∏_{p ≤ Q} (1 + c_p)`, 再经
  `1 + u ≤ exp u` 与 Mertens 第二定理 (`mertensSecond_nat`):
  `Σ_{q ≤ Q} μ²(q)·3^{ω(q)}/φ(q) ≤ C·log⁶(Q+2)`.

## 红队注记 (对装配的真实约束)

两个因子都是**多对数**增长 (乘积 ≈ `xX·polylog(xX)`), 而 `PanMainTermBound`
与 `PanMainTermSieveBound` 声称 `C·xX/log^A(xX)` — 单靠 §3--§4 的初等估计
**无法**把 `xX·polylog` 吸收进 `xX/log^A(xX)` (a = 1, q = 2, y = xX 项单独就有
`li(xX)/φ(2) ≈ xX/log(xX)`). 经典证明中 li 主项被**筛主项** (正主项
`x/log x·∏(1-ν(p))`) 吸收, 只余 `O(x/log^A x)`; 这个吸收机制是
`PanMainTermSieveBound` 的解析内容 (Liu §III; HR 1974 Ch.10), 与
`PAN_PROOF_ATLAS.md` 红队注记一致. §5 给出归约链的诚实多对数版本
`panMainWeightedSum_polylog` 作为中间证据, 供装配期与红队审查使用.
-/

import AnalyticNumberTheory.Sieve.PanMeanValueBody
import AnalyticNumberTheory.Mertens.PartialSummation
import AnalyticNumberTheory.Sieve.GoldbachDensity
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

namespace AnalyticNumberTheory.Sieve

open Finset Real

open scoped Classical
open scoped ArithmeticFunction.Moebius

-- 主项 g 函数忽略剩余类参数 l' (li 部分与 l 无关), 抑制相应告警.
set_option linter.unusedVariables false

/-! ## 1. 主项对象: li 内和与去 max 归约 -/

/-- li 主项的内和: `Σ_{a ≤ X} |li(⌊y/a⌋)|` (li 参数为自然除法 `⌊y/a⌋`,
与 `panPieceSum` 中 `g (y / a) q ...` 的截断参数一致). -/
noncomputable def mainTermInnerSum (y X : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X, |logarithmicIntegral ((y / a : ℕ) : ℝ)|

/-- 内和的 y-max: 镜像 `panPieceMaxY` (对 `y ≤ x` 取 max). -/
noncomputable def mainTermInnerSumMax (X x : ℕ) : ℝ :=
  ((Finset.range (x + 1)).image (fun y => mainTermInnerSum y X)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- 加权 totient 倒数和: `Σ_{q ≤ Q} μ²(q)·3^{ω(q)}/φ(q)` (q = 0 项权重为 0). -/
noncomputable def panMainTotientWeightedSum (Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (Q + 1),
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)

/-- 内和非负. -/
theorem mainTermInnerSum_nonneg (y X : ℕ) : 0 ≤ mainTermInnerSum y X := by
  unfold mainTermInnerSum
  exact Finset.sum_nonneg (fun a ha => abs_nonneg _)

/-- 内和 y-max 非负. -/
theorem mainTermInnerSumMax_nonneg (X x : ℕ) : 0 ≤ mainTermInnerSumMax X x := by
  unfold mainTermInnerSumMax
  exact le_trans (mainTermInnerSum_nonneg 0 X)
    (Finset.le_max'
      (s := (Finset.range (x + 1)).image (fun y => mainTermInnerSum y X))
      (x := mainTermInnerSum 0 X)
      (Finset.mem_image.mpr ⟨0, by simp, rfl⟩))

/-- 权重非负: `μ²(q)·3^{ω(q)} ≥ 0`. -/
theorem panMain_weight_nonneg (q : ℕ) :
    0 ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card := by
  exact mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num) _)

/-- **主项单项的三角归约**: 对任意 a,
  `|f(a)·li(⌊y/a⌋)/φ(q)| ≤ |f(a)|·|li(⌊y/a⌋)|/φ(q)` (去 `a.Coprime` 指示函数,
  |f| ≤ 1). 对所有 q 成立 (φ(q) ≥ 0 即够; q = 0 时两侧皆零). -/
private lemma panMain_summand_abs_le (y X q : ℕ) (f : ℕ → ℝ) (a : ℕ)
    (hfb : ∀ a : ℕ, |f a| ≤ 1) :
    |if a.Coprime q then
      f a * (logarithmicIntegral ((y / a : ℕ) : ℝ) / (Nat.totient q : ℝ))
    else 0|
      ≤ |f a| * (|logarithmicIntegral ((y / a : ℕ) : ℝ)| / (Nat.totient q : ℝ)) := by
  by_cases hcop : a.Coprime q
  · rw [if_pos hcop]
    have hφ : (0 : ℝ) ≤ (Nat.totient q : ℝ) := by positivity
    calc
      |f a * (logarithmicIntegral ((y / a : ℕ) : ℝ) / (Nat.totient q : ℝ))|
          = |f a| * |logarithmicIntegral ((y / a : ℕ) : ℝ) / (Nat.totient q : ℝ)| := by
            rw [abs_mul]
      _ = |f a| * (|logarithmicIntegral ((y / a : ℕ) : ℝ)| / (Nat.totient q : ℝ)) := by
            rw [abs_div, abs_of_nonneg hφ]
      _ ≤ |f a| * (|logarithmicIntegral ((y / a : ℕ) : ℝ)| / (Nat.totient q : ℝ)) := le_rfl
  · have hnn : 0 ≤ |f a| * (|logarithmicIntegral ((y / a : ℕ) : ℝ)| /
        (Nat.totient q : ℝ)) := by
      exact mul_nonneg (abs_nonneg _) (div_nonneg (abs_nonneg _) (by positivity))
    simp [hcop, hnn]

/-- **主项片段的点式归约**: `|panPieceSum| ≤ innerSum/φ(q)` (去 max 前).
对 |f| ≤ 1 一致 (界与 l 无关). -/
theorem panMainPieceSum_abs_le (y X q : ℕ) (f : ℕ → ℝ) (l : ℕ)
    (hfb : ∀ a : ℕ, |f a| ≤ 1) :
    |panPieceSum y X q l f (fun y' q' l' => logarithmicIntegral (y' : ℝ) / Nat.totient q')|
      ≤ mainTermInnerSum y X / (Nat.totient q : ℝ) := by
  unfold panPieceSum mainTermInnerSum
  calc
    |∑ a ∈ Finset.Icc 1 X,
        if a.Coprime q then
          f a * (logarithmicIntegral ((y / a : ℕ) : ℝ) / (Nat.totient q : ℝ))
        else 0|
        ≤ ∑ a ∈ Finset.Icc 1 X,
            |if a.Coprime q then
              f a * (logarithmicIntegral ((y / a : ℕ) : ℝ) / (Nat.totient q : ℝ))
            else 0| := by
          exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.Icc 1 X,
          |f a| * (|logarithmicIntegral ((y / a : ℕ) : ℝ)| / (Nat.totient q : ℝ)) := by
          apply Finset.sum_le_sum
          intro a ha
          exact panMain_summand_abs_le y X q f a hfb
    _ ≤ ∑ a ∈ Finset.Icc 1 X,
          |logarithmicIntegral ((y / a : ℕ) : ℝ)| / (Nat.totient q : ℝ) := by
          apply Finset.sum_le_sum
          intro a ha
          have hφ : (0 : ℝ) ≤ (Nat.totient q : ℝ) := by positivity
          have hnn : 0 ≤ |logarithmicIntegral ((y / a : ℕ) : ℝ)| / (Nat.totient q : ℝ) :=
            div_nonneg (abs_nonneg _) hφ
          calc
            |f a| * (|logarithmicIntegral ((y / a : ℕ) : ℝ)| / (Nat.totient q : ℝ))
                ≤ 1 * (|logarithmicIntegral ((y / a : ℕ) : ℝ)| / (Nat.totient q : ℝ)) :=
                  mul_le_mul_of_nonneg_right (hfb a) hnn
            _ = |logarithmicIntegral ((y / a : ℕ) : ℝ)| / (Nat.totient q : ℝ) := by simp
    _ = (∑ a ∈ Finset.Icc 1 X, |logarithmicIntegral ((y / a : ℕ) : ℝ)|) /
          (Nat.totient q : ℝ) := by
          rw [← Finset.sum_div]

/-- **l-max 归约**: `panPieceMaxL ≤ innerSum/φ(q)` (界与 l 无关, 故 max 直接
进入; q ≤ 1 时 l-集为空, 两侧皆非负平凡). -/
theorem panMainPieceMaxL_le (y X q : ℕ) (f : ℕ → ℝ) (hfb : ∀ a : ℕ, |f a| ≤ 1) :
    panPieceMaxL y X q f (fun y' q' l' => logarithmicIntegral (y' : ℝ) / Nat.totient q') ≤
      mainTermInnerSum y X / (Nat.totient q : ℝ) := by
  unfold panPieceMaxL
  by_cases hS : ((Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q)).Nonempty
  · dsimp only []
    rw [dif_pos hS]
    apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨l, hl, rfl⟩
    exact panMainPieceSum_abs_le y X q f l hfb
  · dsimp only []
    rw [dif_neg hS]
    exact div_nonneg (mainTermInnerSum_nonneg y X)
      (by positivity : (0 : ℝ) ≤ (Nat.totient q : ℝ))

/-- **y-max 归约**: `panPieceMaxY ≤ innerSumMax/φ(q)` (逐 y 的
`panPieceMaxL ≤ innerSum/φ(q)` 后取 max). -/
theorem panMainPieceMaxY_le (X q x : ℕ) (f : ℕ → ℝ) (hfb : ∀ a : ℕ, |f a| ≤ 1) :
    panPieceMaxY X q x f (fun y' q' l' => logarithmicIntegral (y' : ℝ) / Nat.totient q') ≤
      mainTermInnerSumMax X x / (Nat.totient q : ℝ) := by
  unfold panPieceMaxY mainTermInnerSumMax
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  calc
    panPieceMaxL y X q f (fun y' q' l' => logarithmicIntegral (y' : ℝ) / Nat.totient q')
        ≤ mainTermInnerSum y X / (Nat.totient q : ℝ) := panMainPieceMaxL_le y X q f hfb
    _ ≤ mainTermInnerSumMax X x / (Nat.totient q : ℝ) := by
          exact div_le_div_of_nonneg_right
            (Finset.le_max'
              (s := (Finset.range (x + 1)).image (fun y => mainTermInnerSum y X))
              (x := mainTermInnerSum y X)
              (Finset.mem_image.mpr ⟨y, hy, rfl⟩))
            (by positivity : (0 : ℝ) ≤ (Nat.totient q : ℝ))

/-- **带权重的 q-求和归约**: 主项对象 ≤ `innerSumMax · Σ_{q ≤ Q} μ²3^ω/φ(q)`
(q = 0 项权重为零, 平凡; 其余 q 用逐 q 归约 + 权重非负). -/
theorem panMainWeightedSum_le (X Q x : ℕ) (f : ℕ → ℝ) (hfb : ∀ a : ℕ, |f a| ≤ 1) :
    (∑ q ∈ Finset.range (Q + 1),
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
        panPieceMaxY X q x f (fun y' q' l' => logarithmicIntegral (y' : ℝ) / Nat.totient q')) ≤
      mainTermInnerSumMax X x *
        (∑ q ∈ Finset.range (Q + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) := by
  calc
    (∑ q ∈ Finset.range (Q + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panPieceMaxY X q x f (fun y' q' l' => logarithmicIntegral (y' : ℝ) / Nat.totient q'))
        ≤ ∑ q ∈ Finset.range (Q + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              (mainTermInnerSumMax X x / (Nat.totient q : ℝ)) := by
          apply Finset.sum_le_sum
          intro q hq
          exact mul_le_mul_of_nonneg_left (panMainPieceMaxY_le X q x f hfb)
            (panMain_weight_nonneg q)
    _ = mainTermInnerSumMax X x *
          (∑ q ∈ Finset.range (Q + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          ring

/-! ## 2. 解析台阶与归约定理 -/

/-- **解析台阶 (li 主项界, 开放)**: 对每个 `A > 0` 存在 `C > 0, B, x₀`,
使对所有 `X ≥ x₀` 与 `Q := (xX)^{1/2}/log^B(xX)`,

  `innerSumMax(X, ⌊xX⌋) · Σ_{q ≤ Q} μ²(q)·3^{ω(q)}/φ(q) ≤ C·xX/log^A(xX)`,

其中 `innerSumMax(X, x) = max_{y ≤ x} Σ_{a ≤ X} |li(⌊y/a⌋)|`.

这是 `PanMainTermBound` 归约后剩下的唯一解析输入. 经典证明 (Liu 2022 §III;
HR 1974 Ch.10) 中 li 主项被筛主项 (`x/log x·∏(1-ν(p))`) 吸收, 余项给出
`x/log^A x` 的界; 本仓库的初等材料 (§3--§4) 提供两个因子的多对数估计
(`innerSumMax ≪ x·log X`, `Σ μ²3^ω/φ(q) ≪ log⁶Q`), 但多对数乘积累积后
不能直接吸收进 `x/log^A x` (见模块头红队注记) — 吸收机制本身是经典解析
内容, 保留为本台阶. 对 `|f| ≤ 1` 一致. -/
def PanMainTermSieveBound (x : ℕ → ℝ) (f : ℕ → ℝ) : Prop :=
  (∀ a : ℕ, |f a| ≤ 1) ∧
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
      ∀ X : ℕ, x₀ ≤ X →
        mainTermInnerSumMax X (Nat.floor (x X)) *
          (∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) ≤
          C * x X / (log (x X)) ^ A

/-- **T3 归约定理**: `PanMainTermSieveBound` (开放解析台阶) ⇒
  `PanMainTermBound` (主项界). 全部有限代数 (三角不等式, |f| ≤ 1, l-max/y-max
  归约, 权重非负, q = 0 零权重) 在此证明; 唯一解析输入是台阶本身. -/
theorem PanMainTermBound.of_sieveBound {x : ℕ → ℝ} {f : ℕ → ℝ}
    (hS : PanMainTermSieveBound x f) : PanMainTermBound x f := by
  rcases hS with ⟨hfb, hBound⟩
  intro A hA
  rcases hBound A hA with ⟨C, hC, B, x₀, hMain⟩
  refine ⟨C, hC, B, x₀, ?_⟩
  intro X hX
  calc
    (∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panPieceMaxY X q (Nat.floor (x X)) f
            (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q))
        ≤ mainTermInnerSumMax X (Nat.floor (x X)) *
            (∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
              ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) :=
          panMainWeightedSum_le X (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B))
            (Nat.floor (x X)) f hfb
    _ ≤ C * x X / (log (x X)) ^ A := hMain X hX

/-! ## 3. li 的初等界与 y,a 因子的多对数界

主项内和的初等估计: `|li(m)| ≤ m/log 2` (所有自然数 m; m ≥ 2 时
`li(m) = m/log m ≤ m/log 2`, m ≤ 1 时 li(m) = 0), 从而

  `Σ_{a ≤ X} |li(⌊y/a⌋)| ≤ (y/log 2)·(1 + log X)`
  (调和级数 `Σ 1/a ≤ 1 + log X` + `⌊y/a⌋ ≤ y/a`), 再对 y ≤ x 取 max 得
  `mainTermInnerSumMax ≤ (x/log 2)·(1 + log X)`.

这是 `PanMainTermSieveBound` 中 y,a 因子的多对数界 (经典更精细版本
`Σ 1/(a·log(y/a)) ≪ log log X` 见 Mertens 部分和, 此处取充分粗糙的
`log X` 界, 多对数幂次不敏感).
-/

/-- li 的初等一致界: 对所有自然数 m, `|li(m)| ≤ m/log 2`
(li(0) = li(1) = 0, m ≥ 2 时 `li(m) = m/log m ≤ m/log 2`). -/
theorem logIntegral_nat_abs_le (m : ℕ) :
    |logarithmicIntegral (m : ℝ)| ≤ (m : ℝ) / Real.log 2 := by
  unfold logarithmicIntegral
  by_cases hm : m ≤ 1
  · have hzero : (m : ℝ) / Real.log (m : ℝ) = 0 := by
      interval_cases m <;> simp [Real.log_zero, Real.log_one]
    rw [hzero]
    simp only [abs_zero]
    exact div_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ))
      (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  · have hm2 : 2 ≤ m := by omega
    have hlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
    have hm_pos : 0 < (m : ℝ) := by positivity
    have hle_log : Real.log 2 ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hm2)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    calc
      |(m : ℝ) / Real.log (m : ℝ)| = (m : ℝ) / Real.log (m : ℝ) := by
        rw [abs_of_pos (div_pos hm_pos hlog)]
      _ ≤ (m : ℝ) / Real.log 2 := by
        exact div_le_div_of_nonneg_left (le_of_lt hm_pos) hlog2 hle_log

/-- **主项内和的多对数界**: `Σ_{a ≤ X} |li(⌊y/a⌋)| ≤ (y/log 2)·(1 + log X)`
(对 |f| ≤ 1 的主项 y,a 因子; 调和级数 + floor ≤ 值 + |li(m)| ≤ m/log 2). -/
theorem mainTermInnerSum_le (X y : ℕ) :
    mainTermInnerSum y X ≤ (y : ℝ) / Real.log 2 * (1 + Real.log (X : ℝ)) := by
  unfold mainTermInnerSum
  calc
    (∑ a ∈ Finset.Icc 1 X, |logarithmicIntegral ((y / a : ℕ) : ℝ)|)
        ≤ ∑ a ∈ Finset.Icc 1 X, ((y / a : ℕ) : ℝ) / Real.log 2 := by
          apply Finset.sum_le_sum
          intro a ha
          exact logIntegral_nat_abs_le (y / a)
    _ = (∑ a ∈ Finset.Icc 1 X, ((y / a : ℕ) : ℝ)) / Real.log 2 := by
          rw [← Finset.sum_div]
    _ ≤ (∑ a ∈ Finset.Icc 1 X, (y : ℝ) / (a : ℝ)) / Real.log 2 := by
          exact div_le_div_of_nonneg_right
            (Finset.sum_le_sum (fun a ha => Nat.cast_div_le)) (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
    _ = ((y : ℝ) * (∑ a ∈ Finset.Icc 1 X, 1 / (a : ℝ))) / Real.log 2 := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          ring
    _ ≤ (y : ℝ) * (1 + Real.log (X : ℝ)) / Real.log 2 := by
          have hfac : (∑ a ∈ Finset.Icc 1 X, 1 / (a : ℝ)) = (harmonic X : ℝ) := by
            have hq' : harmonic X = ∑ a ∈ Finset.Icc 1 X, (1 : ℚ) / (a : ℚ) := by
              simpa [one_div] using harmonic_eq_sum_Icc (n := X)
            have hcast : (↑(∑ a ∈ Finset.Icc 1 X, (1 : ℚ) / (a : ℚ)) : ℝ) =
                ∑ a ∈ Finset.Icc 1 X, (1 : ℝ) / (a : ℝ) := by
              rw [Rat.cast_sum]
              apply Finset.sum_congr rfl
              intro a ha
              rw [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
            calc
              (∑ a ∈ Finset.Icc 1 X, 1 / (a : ℝ)) =
                  (↑(∑ a ∈ Finset.Icc 1 X, (1 : ℚ) / (a : ℚ)) : ℝ) := by
                rw [hcast]
              _ = (harmonic X : ℝ) := by
                rw [hq']
          have hle : (∑ a ∈ Finset.Icc 1 X, 1 / (a : ℝ)) ≤ 1 + Real.log (X : ℝ) := by
            rw [hfac]
            exact harmonic_le_one_add_log X
          have hy : (0 : ℝ) ≤ (y : ℝ) := by positivity
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle hy)
            (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
    _ = (y : ℝ) / Real.log 2 * (1 + Real.log (X : ℝ)) := by ring

/-- **主项内和 y-max 的多对数界**:
  `max_{y ≤ x} Σ_{a ≤ X} |li(⌊y/a⌋)| ≤ (x/log 2)·(1 + log X)`. -/
theorem mainTermInnerSumMax_le (X x : ℕ) :
    mainTermInnerSumMax X x ≤ (x : ℝ) / Real.log 2 * (1 + Real.log (X : ℝ)) := by
  unfold mainTermInnerSumMax
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  have hyx : y ≤ x := Nat.le_of_lt_succ (Finset.mem_range.mp hy)
  have hlogX : (0 : ℝ) ≤ 1 + Real.log (X : ℝ) := by
    by_cases hX : X = 0
    · subst X
      simp [Real.log_zero]
    · have hX1 : 1 ≤ X := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hX)
      have hlog : (0 : ℝ) ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX1)
      linarith
  calc
    mainTermInnerSum y X ≤ (y : ℝ) / Real.log 2 * (1 + Real.log (X : ℝ)) :=
      mainTermInnerSum_le X y
    _ ≤ (x : ℝ) / Real.log 2 * (1 + Real.log (X : ℝ)) := by
          exact mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (by exact_mod_cast hyx)
              (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))) hlogX

/-! ## 4. 加权 totient 倒数和的多对数界 (Mertens 第二定理 + Euler 积展开)

q 因子的估计: `Σ_{q ≤ Q} μ²(q)·3^{ω(q)}/φ(q) ≤ C·log⁶Q`. 证明链:

```text
Σ_{q ≤ Q} μ²3^ω/φ(q)
  = Σ_{q ≤ Q, sqfree} μ²3^ω/φ(q)                    -- 非平方自由项 μ = 0
  = Σ_{q ≤ Q, sqfree} ∏_{p|q} 3/(p-1)              -- goldbachNu = 1/φ, 3^ω = ∏3, μ² = 1
  ≤ ∏_{p ≤ Q, p prime} (1 + 3/(p-1))               -- q ↦ q.primeFactors 单射入子集
  ≤ exp(Σ_{p ≤ Q} 3/(p-1))                         -- 1 + u ≤ exp u
  ≤ exp(6·Σ_{p ≤ Q} 1/p)                           -- 3/(p-1) ≤ 6/p (p ≥ 2)
  ≤ exp(6·(log log Q + O(1)))                      -- Mertens 第二定理 (mertensSecond_nat)
  = e^{O(1)}·(log Q)^6
```

最后一行的常数由 `mertensSecond_nat` 的误差项在 `Q ≥ 3` 下吸收. 这是
`PanMainTermSieveBound` 中 q 因子的多对数界 (经典 `Σ μ²3^ω/φ(q) ≪ log³Q`
见 Liu 2022 §III; 此处取充分的幂次 6 以匹配 `3/(p-1) ≤ 6/p` 的粗界).
-/

section

open AnalyticNumberTheory.Mertens

/-- c_p = 3/(p-1) 对素数 p 非负. -/
private lemma panMain_cp_nonneg {p : ℕ} (hp : p.Prime) :
    (0 : ℝ) ≤ 3 / ((p : ℝ) - 1) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hden : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  exact div_nonneg (by norm_num : (0 : ℝ) ≤ 3) hden

/-- c_p ≤ 6/p 对素数 p (p ≥ 2). -/
private lemma panMain_cp_le_six_div {p : ℕ} (hp : p.Prime) :
    (3 : ℝ) / ((p : ℝ) - 1) ≤ 6 / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hden1 : 0 < (p : ℝ) - 1 := by linarith
  have hden2 : 0 < (p : ℝ) := by positivity
  rw [div_le_div_iff₀ hden1 hden2]
  nlinarith

/-- 平方自由 q 的素因子积: `q = ∏_{p|q} p`. -/
private lemma sqfree_eq_prod_primeFactors {q : ℕ} (hq : Squarefree q) :
    q = ∏ p ∈ q.primeFactors, p := by
  have hq0 : q ≠ 0 := by
    intro h
    subst q
    exact not_squarefree_zero hq
  have hprod := Nat.prod_primeFactors_pow_factorization hq0
  have hsq : ∀ p ∈ q.primeFactors, q.factorization p = 1 := by
    intro p hp
    exact Nat.factorization_eq_one_of_squarefree hq (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  calc
    q = ∏ p ∈ q.primeFactors, p ^ q.factorization p := hprod
    _ = ∏ p ∈ q.primeFactors, p := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [hsq p hp, pow_one]

/-- **平方自由 q 的单项重写**: `μ²(q)·3^{ω(q)}/φ(q) = ∏_{p|q} 3/(p-1)`
(`μ² = 1`, `3^{ω} = ∏3`, `1/φ = goldbachNu q = ∏ 1/(p-1)`). -/
private lemma panMain_weight_sqfree_eq_prod (q : ℕ) (hq : Squarefree q) :
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ) =
      ∏ p ∈ q.primeFactors, (3 : ℝ) / ((p : ℝ) - 1) := by
  have hq0 : q ≠ 0 := by
    intro h
    subst q
    exact not_squarefree_zero hq
  have hμ : ((μ q : ℤ) : ℝ) ^ 2 = 1 := by
    have hμz : (μ q : ℤ) = (-1 : ℤ) ^ ArithmeticFunction.cardFactors q := by
      exact ArithmeticFunction.moebius_apply_of_squarefree hq
    rw [hμz]
    norm_num [Int.cast_pow, Int.cast_neg, Int.cast_one]
    exact neg_one_pow_eq_or ℝ (ArithmeticFunction.cardFactors q)
  have h3 : (3 : ℝ) ^ q.primeFactors.card = ∏ p ∈ q.primeFactors, (3 : ℝ) := by
    rw [Finset.prod_const]
  have hphi : (1 : ℝ) / (Nat.totient q : ℝ) =
      ∏ p ∈ q.primeFactors, (1 : ℝ) / ((p : ℝ) - 1) := by
    rw [← goldbachNu_squarefree_eq_inv_totient hq]
    unfold goldbachNu
    rw [ArithmeticFunction.prodPrimeFactors_apply hq0]
  calc
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)
        = ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            (1 / (Nat.totient q : ℝ)) := by
          ring
    _ = 1 * (∏ p ∈ q.primeFactors, (3 : ℝ)) * (∏ p ∈ q.primeFactors, (1 : ℝ) / ((p : ℝ) - 1)) := by
          rw [hμ, h3, hphi]
    _ = (∏ p ∈ q.primeFactors, (3 : ℝ)) * (∏ p ∈ q.primeFactors, (1 : ℝ) / ((p : ℝ) - 1)) := by
          simp
    _ = ∏ p ∈ q.primeFactors, (3 : ℝ) / ((p : ℝ) - 1) := by
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro p hp
          ring

/-- 子集和展开: `Σ_{S ⊆ F} ∏_{p∈S} c_p = ∏_{p∈F} (1 + c_p)`
(按 F 归纳; 正合等式, 无需非负). -/
private lemma panMain_powerset_prod_eq (F : Finset ℕ) (c : ℕ → ℝ) :
    (∑ S ∈ F.powerset, ∏ p ∈ S, c p) = ∏ p ∈ F, (1 + c p) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F ha ih =>
      have hdisj : Disjoint F.powerset (F.powerset.image (fun S => insert a S)) := by
        rw [Finset.disjoint_left]
        intro S hS1 hS2
        rcases Finset.mem_image.mp hS2 with ⟨T, hT, rfl⟩
        have haS : a ∈ insert a T := Finset.mem_insert_self a T
        exact ha ((Finset.mem_powerset.mp hS1) haS)
      calc
        (∑ S ∈ (insert a F).powerset, ∏ p ∈ S, c p)
            = (∑ S ∈ F.powerset, ∏ p ∈ S, c p) +
                (∑ S ∈ (F.powerset.image (fun S => insert a S)), ∏ p ∈ S, c p) := by
              rw [Finset.powerset_insert, Finset.sum_union hdisj]
        _ = (∑ S ∈ F.powerset, ∏ p ∈ S, c p) +
              (∑ S ∈ F.powerset, ∏ p ∈ insert a S, c p) := by
              congr 1
              rw [Finset.sum_image]
              · rfl
              · intro S hS T hT hST
                have haS : a ∉ S := fun has => ha ((Finset.mem_powerset.mp hS) has)
                have haT : a ∉ T := fun hat => ha ((Finset.mem_powerset.mp hT) hat)
                ext x
                constructor
                · intro hx
                  have hxT : x ∈ insert a T := by rwa [← hST]
                  rcases Finset.mem_insert.mp hxT with hxT' | hxa
                  · exact hxT'
                  · subst x
                    exact (haS hx).elim
                · intro hx
                  have hxS : x ∈ insert a S := by rwa [hST]
                  rcases Finset.mem_insert.mp hxS with hxS' | hxa
                  · exact hxS'
                  · subst x
                    exact (haT hx).elim
        _ = (∑ S ∈ F.powerset, ∏ p ∈ S, c p) + c a * (∑ S ∈ F.powerset, ∏ p ∈ S, c p) := by
              congr 1
              rw [← Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro S hS
              have haS : a ∉ S := fun has => ha ((Finset.mem_powerset.mp hS) has)
              rw [Finset.prod_insert haS]
        _ = (1 + c a) * (∑ S ∈ F.powerset, ∏ p ∈ S, c p) := by ring
        _ = (1 + c a) * (∏ p ∈ F, (1 + c p)) := by rw [ih]
        _ = ∏ p ∈ insert a F, (1 + c p) := by rw [Finset.prod_insert ha]

/-- 平方自由 q ≤ Q 的 `∏_{p|q} c_p` 和 ≤ 素因子子集展开
`∏_{p ≤ Q, prime} (1 + c_p)` (q ↦ q.primeFactors 单射入 `primesUpTo Q`
的幂集, 再展开). -/
private lemma panMain_sqfree_sum_le_prod (Q : ℕ) (c : ℕ → ℝ) (hc : ∀ p, p.Prime → 0 ≤ c p) :
    (∑ q ∈ (Finset.range (Q + 1)).filter Squarefree, ∏ p ∈ q.primeFactors, c p) ≤
      ∏ p ∈ primesUpTo Q, (1 + c p) := by
  let Fq : Finset ℕ := (Finset.range (Q + 1)).filter Squarefree
  let F : Finset ℕ := primesUpTo Q
  have hinj : Set.InjOn (fun q : ℕ => q.primeFactors) (↑Fq : Set ℕ) := by
    intro q hq r hr hpf
    have hqsq : Squarefree q := (Finset.mem_filter.mp hq).2
    have hrsq : Squarefree r := (Finset.mem_filter.mp hr).2
    calc
      q = ∏ p ∈ q.primeFactors, p := (sqfree_eq_prod_primeFactors hqsq).symm
      _ = ∏ p ∈ r.primeFactors, p := by rw [hpf]
      _ = r := sqfree_eq_prod_primeFactors hrsq
  have hsubset : Fq.image (fun q => q.primeFactors) ⊆ F.powerset := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨q, hq, rfl⟩
    rw [Finset.mem_powerset]
    intro p hp
    have hqsq : Squarefree q := (Finset.mem_filter.mp hq).2
    have hq0 : q ≠ 0 := by
      intro h
      subst q
      exact not_squarefree_zero hqsq
    have hqrange : q ∈ Finset.range (Q + 1) := (Finset.mem_filter.mp hq).1
    have hqle : q ≤ Q := Nat.le_of_lt_succ (Finset.mem_range.mp hqrange)
    rw [mem_primesUpTo]
    constructor
    · exact Nat.prime_of_mem_primeFactors hp
    · exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) (Nat.dvd_of_mem_primeFactors hp)) hqle
  calc
    (∑ q ∈ Fq, ∏ p ∈ q.primeFactors, c p)
        = ∑ S ∈ Fq.image (fun q => q.primeFactors), ∏ p ∈ S, c p := by
          rw [← Finset.sum_image hinj]
    _ ≤ ∑ S ∈ F.powerset, ∏ p ∈ S, c p := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun S hS hnot => by
            apply Finset.prod_nonneg
            intro p hp
            have hpF : p ∈ F := (Finset.mem_powerset.mp hS) hp
            exact hc p (mem_primesUpTo.mp hpF).1)
    _ = ∏ p ∈ F, (1 + c p) := panMain_powerset_prod_eq F c

/-- `∏_{p∈F} (1 + c p) ≤ exp(Σ_{p∈F} c p)` 对 `c ≥ 0` (1 + u ≤ exp u 逐因子). -/
private lemma panMain_prod_one_add_le_exp (F : Finset ℕ) (c : ℕ → ℝ)
    (hc : ∀ p ∈ F, 0 ≤ c p) :
    (∏ p ∈ F, (1 + c p)) ≤ rexp (∑ p ∈ F, c p) := by
  calc
    (∏ p ∈ F, (1 + c p)) ≤ ∏ p ∈ F, rexp (c p) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hcp : 0 ≤ c p := hc p hp
        linarith
      · intro p hp
        simpa [add_comm] using (Real.add_one_le_exp (c p))
    _ = rexp (∑ p ∈ F, c p) := by
      classical
      induction F using Finset.induction_on with
      | empty => simp
      | insert a F ha ih =>
          rw [Finset.prod_insert ha, Finset.sum_insert ha]
          rw [Real.exp_add]
          rw [ih]

/-- **加权 totient 倒数和的多对数界**: 对 `Q ≥ 3`,
`Σ_{q ≤ Q} μ²(q)·3^{ω(q)}/φ(q) ≤ C·(log Q)^6` (Mertens 第二定理 +
Euler 积展开). -/
theorem panMainTotientWeightedSum_le (Q : ℕ) (hQ : 3 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ panMainTotientWeightedSum Q ≤ C * (Real.log (Q : ℝ)) ^ 6 := by
  rcases mertensSecond_nat with ⟨C₀, hC₀, hM₀⟩
  let K : ℝ := 6 * mertensSecondConstant + 6 * C₀ / Real.log 3
  let c : ℕ → ℝ := fun p => (3 : ℝ) / ((p : ℝ) - 1)
  have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Q))
  refine ⟨rexp K, Real.exp_pos K, ?_⟩
  calc
    panMainTotientWeightedSum Q
        = ∑ q ∈ Finset.range (Q + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ) := rfl
    _ = ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree,
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ) := by
          rw [← Finset.sum_filter_of_ne]
          intro q hq hterm
          have hμ2 : ((μ q : ℤ) : ℝ) ^ 2 ≠ 0 := by
            intro hμ2
            apply hterm
            rw [hμ2]
            simp
          have hμz : (μ q : ℤ) ≠ 0 := by
            intro hμz
            exact hμ2 (by simp [hμz])
          exact (ArithmeticFunction.moebius_ne_zero_iff_squarefree).mp hμz
    _ = ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree, ∏ p ∈ q.primeFactors, c p := by
          dsimp [c]
          apply Finset.sum_congr rfl
          intro q hq
          exact panMain_weight_sqfree_eq_prod q (Finset.mem_filter.mp hq).2
    _ ≤ ∏ p ∈ primesUpTo Q, (1 + c p) := by
          exact panMain_sqfree_sum_le_prod Q c (fun p hp => panMain_cp_nonneg hp)
    _ ≤ rexp (∑ p ∈ primesUpTo Q, c p) := by
          exact panMain_prod_one_add_le_exp (primesUpTo Q) c (fun p hp => panMain_cp_nonneg (mem_primesUpTo.mp hp).1)
    _ ≤ rexp (∑ p ∈ primesUpTo Q, (6 : ℝ) / (p : ℝ)) := by
          apply Real.exp_le_exp.mpr
          apply Finset.sum_le_sum
          intro p hp
          exact panMain_cp_le_six_div (mem_primesUpTo.mp hp).1
    _ = rexp (6 * primeReciprocalSum Q) := by
          have hsum : (∑ p ∈ primesUpTo Q, (6 : ℝ) / (p : ℝ)) = 6 * primeReciprocalSum Q := by
            unfold primeReciprocalSum
            rw [← Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p hp
            ring
          rw [hsum]
    _ ≤ rexp (6 * (Real.log (Real.log (Q : ℝ)) + mertensSecondConstant + C₀ / Real.log (Q : ℝ))) := by
          have hP : primeReciprocalSum Q ≤
              Real.log (Real.log (Q : ℝ)) + mertensSecondConstant + C₀ / Real.log (Q : ℝ) := by
            have h := hM₀ Q (by omega : 2 ≤ Q)
            have hle : primeReciprocalSum Q - (Real.log (Real.log (Q : ℝ)) + mertensSecondConstant) ≤
                C₀ / Real.log (Q : ℝ) := (abs_le.mp h).2
            linarith
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left hP (by norm_num : (0 : ℝ) ≤ 6)
    _ ≤ rexp (6 * Real.log (Real.log (Q : ℝ)) + K) := by
          apply Real.exp_le_exp.mpr
          have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
          have hclog : C₀ / Real.log (Q : ℝ) ≤ C₀ / Real.log 3 := by
            have hlogQ3 : Real.log 3 ≤ Real.log (Q : ℝ) :=
              Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by exact_mod_cast hQ)
            exact div_le_div_of_nonneg_left hC₀.le hlog3 hlogQ3
          dsimp [K]
          linarith
    _ = (Real.log (Q : ℝ)) ^ 6 * rexp K := by
          have hpow : rexp (6 * Real.log (Real.log (Q : ℝ))) = (Real.log (Q : ℝ)) ^ 6 := by
            calc
              rexp (6 * Real.log (Real.log (Q : ℝ)))
                  = rexp (Real.log (Real.log (Q : ℝ)) * 6) := by
                    congr 1
                    ring
              _ = rexp (Real.log (Real.log (Q : ℝ))) ^ 6 :=
                Real.exp_mul (Real.log (Real.log (Q : ℝ))) 6
              _ = (Real.log (Q : ℝ)) ^ 6 := by
                    rw [Real.exp_log hlogQ]
          calc
            rexp (6 * Real.log (Real.log (Q : ℝ)) + K)
                = rexp (6 * Real.log (Real.log (Q : ℝ))) * rexp K := by
                  rw [Real.exp_add]
            _ = (Real.log (Q : ℝ)) ^ 6 * rexp K := by rw [hpow]
    _ = rexp K * (Real.log (Q : ℝ)) ^ 6 := by ring

end

end AnalyticNumberTheory.Sieve
