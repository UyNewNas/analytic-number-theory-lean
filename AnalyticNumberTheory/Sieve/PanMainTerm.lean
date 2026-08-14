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

两个因子都是**多对数**增长 (乘积 ≈ `xX·polylog(xX)`). 旧陈述声称
`PanMainTermBound` 与 `PanMainTermSieveBound` 有 `C·xX/log^A(xX)` 界 —
单靠 §3--§4 的初等估计**无法**把 `xX·polylog` 吸收进 `xX/log^A(xX)`
(a = 1, q = 2, y = xX 项单独就有 `li(xX)/φ(2) ≈ xX/log(xX)`); 事实上该陈述
对典型实例 `x X = X` 即**为假** (§6 红队注记给出反例). 经典证明中 li 主项被
**筛主项** (正主项 `x/log x·∏(1-ν(p))`) **相减吸收**, 只余 `O(x/log^A x)`;
这个吸收机制需要筛积对象 (Liu §III; HR 1974 Ch.10; ROADMAP BRG 节点), 与
`PAN_PROOF_ATLAS.md` 红队注记一致. 本文件 (PR #41 之后) 把三个台阶的 RHS
修正为**可证的多对数形式** `C·xX·(log xX)^{A+7}` (`PanMainSieveAbsorption`
§6 已证明: 固定多对数因子被更大的 log 幂次最终压制), §5 的
`panMainWeightedSum_polylog` 作为中间证据供装配期与红队审查使用.

## 状态 (线 T3i)

- §4 已实现: `panMainTotientWeightedSum_le_polylog` (q 因子 `C·log⁶(Q+2)`, 全证).
- §5 已实现: `panMainWeightedSum_polylog` (诚实多对数版主项界, 全证).
- §6 已实现 (**红队修正, PR #41 之后**): 解析吸收台阶 `PanMainSieveAbsorption`
  改为可证的多对数形式 (`≤ C·xX·(log xX)^{A+7}`, 假设 `X ≤ x X`; 旧
  `C·xX/log^A(xX)` 形式对 `1 < x X` 为假, 见 §6 红队注记) 并由
  `panMainSieveAbsorption_of_dom` **证明** (log 最终压制, §6.1, 零 sorry);
  `PanMainTermSieveBound` 同步改为多对数 RHS,
  `PanMainTermSieveBound.of_innerSumBound` (`PanMainSieveAbsorption` ⇒
  `PanMainTermSieveBound`; 全部有限部分在此证明). 经典 `C·xX/log^A(xX)`
  形式保留为 BRG 节点 (筛主项相减吸收) 的开放目标.
-/

import AnalyticNumberTheory.Sieve.PanMeanValueBody
import AnalyticNumberTheory.Mertens.PartialSummation
import AnalyticNumberTheory.Sieve.GoldbachDensity
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

namespace AnalyticNumberTheory.Sieve

open Finset Real
open AnalyticNumberTheory.Mertens

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

/-- **解析台阶 (li 主项界, 多对数形式)**: 对每个 `A > 0` 存在 `C > 0, B, x₀`,
使对所有 `X ≥ x₀` 与 `Q := (xX)^{1/2}/log^B(xX)`,

  `innerSumMax(X, ⌊xX⌋) · Σ_{q ≤ Q} μ²(q)·3^{ω(q)}/φ(q) ≤ C·xX·(log xX)^{A+7}`,

其中 `innerSumMax(X, x) = max_{y ≤ x} Σ_{a ≤ X} |li(⌊y/a⌋)|`.

**红队修正 (相对 PR #34/#41 的旧陈述)**: 旧陈述 RHS 为 `C·xX/log^A(xX)` —
对 `li` 主项片段本身为假 (e.g. `x X = X`, A = 2 时左侧 ≥ `li(X)·1 ~ X/log X`
而右侧 ~ `C·X/log²X`; 更一般地 `x·polylog` 不能被 `x/log^A x` 吸收, 见 §6
红队注记). 经典证明中 li 主项被筛主项 (`x/log x·∏(1-ν(p))`, Liu 2022 §III;
HR 1974 Ch.10) **相减吸收**, 只余 `O(x/log^A x)` — 那需要筛积对象, 是
`PanMainTermBound` 级别的解析内容 (见 `PAN_PROOF_ATLAS.md` 红队注记与
ROADMAP BRG 节点). 本台阶的正确可证形式: 两个初等因子 (§3--§4) 的多对数积
`xX·(1+log X)·log⁶(xX+2)` 只能被**更大的** log 幂次压制 (总度数 7):
`≤ C·xX·(log xX)^{A+7}` (`PanMainSieveAbsorption`, §6, 已证明). -/
def PanMainTermSieveBound (x : ℕ → ℝ) (f : ℕ → ℝ) : Prop :=
  (∀ a : ℕ, |f a| ≤ 1) ∧
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
      ∀ X : ℕ, x₀ ≤ X →
        mainTermInnerSumMax X (Nat.floor (x X)) *
          (∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) ≤
          C * x X * (log (x X)) ^ (A + 7)

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
    _ ≤ C * x X * (log (x X)) ^ (A + 7) := hMain X hX

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

/-! ## 4. q 因子的多对数界 (加权 totient 倒数和)

平方自由 q 的单项 `μ²(q)·3^{ω(q)}/φ(q) = ∏_{p | q} 3/(p-1)`, 子集展开
`Σ_{q ≤ Q, sqfree} ∏_{p|q} c_p ≤ ∏_{p ≤ Q} (1 + c_p)`, 再经
`∏(1+u) ≤ exp(Σu)` 与 Mertens 第二定理 (`mertensSecond_nat`):

`Σ_{q ≤ Q} μ²(q)·3^{ω(q)}/φ(q) ≤ C·log⁶(Q+2)`.

全部初等 (μ² 在平方自由 q 上 = 1, 非平方自由 = 0; 平方自由 q 与素因子集一一对应;
调和级数 `Σ 1/(p-1) ≤ 2Σ 1/p`; Mertens 第二定理). -/

private lemma squarefree_eq_prod_primeFactors {n : ℕ} (hn : Squarefree n) :
    n = ∏ p ∈ n.primeFactors, p := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact not_squarefree_zero hn
  have hprod : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
    Nat.prod_primeFactors_pow_factorization hn0
  have hsq : ∀ p ∈ n.primeFactors, n.factorization p = 1 := by
    intro p hp
    exact Nat.factorization_eq_one_of_squarefree hn (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  have hpow : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = ∏ p ∈ n.primeFactors, p := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [hsq p hp, pow_one]
  exact hprod.trans hpow

/-- 子集和恒等式: `∏_{x ∈ s} (1 + g x)` 展开为所有子集上的积之和
`Σ_{t ⊆ s} ∏_{x ∈ t} g x`. -/
private lemma sum_powerset_prod {α : Type*} [DecidableEq α] (s : Finset α) (g : α → ℝ) :
    (∑ t ∈ s.powerset, ∏ x ∈ t, g x) = ∏ x ∈ s, (1 + g x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      calc
        (∑ t ∈ (insert a s).powerset, ∏ x ∈ t, g x)
            = (∑ t ∈ s.powerset, ∏ x ∈ t, g x) + ∑ t ∈ s.powerset, ∏ x ∈ insert a t, g x := by
              rw [Finset.sum_powerset_insert ha]
        _ = (∑ t ∈ s.powerset, ∏ x ∈ t, g x) + ∑ t ∈ s.powerset, (g a * ∏ x ∈ t, g x) := by
              congr 1
              apply Finset.sum_congr rfl
              intro t ht
              have hat : a ∉ t := by
                intro hat'
                exact ha ((Finset.mem_powerset.mp ht) hat')
              rw [Finset.prod_insert hat]
        _ = (∑ t ∈ s.powerset, ∏ x ∈ t, g x) + g a * (∑ t ∈ s.powerset, ∏ x ∈ t, g x) := by
              rw [← Finset.mul_sum]
        _ = (1 + g a) * (∑ t ∈ s.powerset, ∏ x ∈ t, g x) := by ring
        _ = (1 + g a) * (∏ x ∈ s, (1 + g x)) := by rw [ih]
        _ = ∏ x ∈ insert a s, (1 + g x) := by rw [Finset.prod_insert ha]

/-- 平方自由 q 的主项权重: `μ²(q)·3^{ω(q)}/φ(q) = ∏_{p | q} 3/(p-1)`. -/
theorem panMainTotientWeight_term_squarefree (q : ℕ) (hq : Squarefree q) :
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ) =
      ∏ p ∈ q.primeFactors, (3 : ℝ) / ((p : ℝ) - 1) := by
  have hmu : ((μ q : ℤ) : ℝ) ^ 2 = 1 := by
    rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hq]
    norm_num
  have hφ : (Nat.totient q : ℝ) = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    rw [totient_eq_prod_primeFactors_of_squarefree hq, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
    rw [Nat.cast_sub hp1]
    norm_num
  calc
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)
        = (3 : ℝ) ^ q.primeFactors.card / (∏ p ∈ q.primeFactors, ((p : ℝ) - 1)) := by
          rw [hmu, hφ]
          norm_num
    _ = (∏ p ∈ q.primeFactors, (3 : ℝ)) / (∏ p ∈ q.primeFactors, ((p : ℝ) - 1)) := by
          rw [← Finset.prod_const]
    _ = ∏ p ∈ q.primeFactors, (3 : ℝ) / ((p : ℝ) - 1) := by
          rw [← Finset.prod_div_distrib]

/-- 非平方自由 q 的主项权重为零 (`μ(q) = 0`). -/
theorem panMainTotientWeight_term_non_squarefree (q : ℕ) (hq : ¬ Squarefree q) :
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ) = 0 := by
  have hmu : (μ q : ℤ) = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq
  simp [hmu]

/-- 主项权重非负 (含 φ 分母). -/
private lemma panMainTotientWeight_term_nonneg (q : ℕ) :
    0 ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ) := by
  exact div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _))
    (by positivity : (0 : ℝ) ≤ (Nat.totient q : ℝ))

/-- **子集展开**: 非负系数下 `Σ_{q ≤ Q, sqfree} ∏_{p | q} c p ≤ ∏_{p ≤ Q} (1 + c p)`.
平方自由 q 与其素因子集一一对应 (`q = ∏ p ∈ q.primeFactors, p`), 而
`∏_{p ≤ Q} (1 + c p)` 展开为所有 `S ⊆ {p ≤ Q}` 的 `∏_{p ∈ S} c p` 之和. -/
theorem sum_squarefree_prod_primeFactors_le_prod_one_add (Q : ℕ) (c : ℕ → ℝ)
    (hc : ∀ p : ℕ, p.Prime → 0 ≤ c p) :
    (∑ q ∈ (Finset.range (Q + 1)).filter Squarefree, ∏ p ∈ q.primeFactors, c p) ≤
      ∏ p ∈ primesUpTo Q, (1 + c p) := by
  classical
  have hg : Set.InjOn (fun q : ℕ => q.primeFactors)
      (↑((Finset.range (Q + 1)).filter Squarefree) : Set ℕ) := by
    intro a ha b hb hgab
    have haSq : Squarefree a := (Finset.mem_filter.mp ha).2
    have hbSq : Squarefree b := (Finset.mem_filter.mp hb).2
    calc
      a = ∏ p ∈ a.primeFactors, p := squarefree_eq_prod_primeFactors haSq
      _ = ∏ p ∈ b.primeFactors, p := by
            have hgab' : a.primeFactors = b.primeFactors := by simpa using hgab
            rw [← hgab']
      _ = b := (squarefree_eq_prod_primeFactors hbSq).symm
  have him : ((Finset.range (Q + 1)).filter Squarefree).image (fun q : ℕ => q.primeFactors) ⊆
      (primesUpTo Q).powerset := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨q, hq, rfl⟩
    rw [Finset.mem_powerset]
    intro p hp
    have hqmem : q ∈ Finset.range (Q + 1) := (Finset.mem_filter.mp hq).1
    have hqSq : Squarefree q := (Finset.mem_filter.mp hq).2
    have hq_le : q ≤ Q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hqmem)
    have hq_ne : q ≠ 0 := by
      intro hq0
      rw [hq0] at hqSq
      exact not_squarefree_zero (R := ℕ) hqSq
    have hp_pr : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_dvd : p ∣ q := Nat.dvd_of_mem_primeFactors hp
    have hp_le_q : p ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq_ne) hp_dvd
    exact (mem_primesUpTo).2 ⟨hp_pr, le_trans hp_le_q hq_le⟩
  calc
    (∑ q ∈ (Finset.range (Q + 1)).filter Squarefree, ∏ p ∈ q.primeFactors, c p)
        = ∑ S ∈ ((Finset.range (Q + 1)).filter Squarefree).image (fun q : ℕ => q.primeFactors),
            ∏ p ∈ S, c p := by
          exact (Finset.sum_image (g := fun q : ℕ => q.primeFactors)
            (f := fun S : Finset ℕ => ∏ p ∈ S, c p) hg).symm
    _ ≤ ∑ S ∈ (primesUpTo Q).powerset, ∏ p ∈ S, c p := by
          exact Finset.sum_le_sum_of_subset_of_nonneg him (fun S hSt hSn => by
            exact Finset.prod_nonneg (fun p hp => hc p
              ((mem_primesUpTo.mp ((Finset.mem_powerset.mp hSt) hp)).1)))
    _ = ∏ p ∈ primesUpTo Q, (1 + c p) := by
          rw [sum_powerset_prod (primesUpTo Q) c]

/-- 加权 totient 倒数和 ≤ 素数 ≤ Q 上的乘积 `∏_{p ≤ Q} (1 + 3/(p-1))`. -/
theorem panMainTotientWeightedSum_le_prod_one_add (Q : ℕ) :
    panMainTotientWeightedSum Q ≤
      ∏ p ∈ primesUpTo Q, (1 + (3 : ℝ) / ((p : ℝ) - 1)) := by
  unfold panMainTotientWeightedSum
  calc
    (∑ q ∈ Finset.range (Q + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ))
        = ∑ q ∈ Finset.range (Q + 1),
            if Squarefree q then
              ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)
            else 0 := by
          apply Finset.sum_congr rfl
          intro q hq
          by_cases h : Squarefree q
          · rw [if_pos h]
          · rw [if_neg h]
            exact panMainTotientWeight_term_non_squarefree q h
    _ = ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree,
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ) := by
          rw [Finset.sum_filter]
    _ = ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree,
          ∏ p ∈ q.primeFactors, (3 : ℝ) / ((p : ℝ) - 1) := by
          apply Finset.sum_congr rfl
          intro q hq
          exact panMainTotientWeight_term_squarefree q (Finset.mem_filter.mp hq).2
    _ ≤ ∏ p ∈ primesUpTo Q, (1 + (3 : ℝ) / ((p : ℝ) - 1)) := by
          exact sum_squarefree_prod_primeFactors_le_prod_one_add Q
            (fun p => (3 : ℝ) / ((p : ℝ) - 1)) (by
              intro p hp
              have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
              have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
              exact div_nonneg (by norm_num : (0 : ℝ) ≤ 3) (le_of_lt hpm1))

/-- 加权 totient 倒数和在 Q 上单调 (权重非负). -/
theorem panMainTotientWeightedSum_mono : Monotone panMainTotientWeightedSum := by
  intro Q₁ Q₂ hQ
  unfold panMainTotientWeightedSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hq) (by omega : Q₁ + 1 ≤ Q₂ + 1))
  · intro q hq hnq
    exact panMainTotientWeight_term_nonneg q

/-- **q 因子的多对数界**: `Σ_{q ≤ Q} μ²(q)·3^{ω(q)}/φ(q) ≤ C·log⁶(Q+2)`.
子集展开 + `∏(1+u) ≤ exp(Σu)` + `Σ_{p ≤ Q} 3/(p-1) ≤ 6·Σ_{p ≤ Q} 1/p` +
Mertens 第二定理; 有限初段 (Q ≤ 2) 吸收进常数. -/
theorem panMainTotientWeightedSum_le_polylog :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ,
      panMainTotientWeightedSum Q ≤ C * (Real.log (Q + 2)) ^ (6 : ℝ) := by
  classical
  obtain ⟨C₁, hC₁, hM⟩ := mertensSecond_nat
  let K : ℝ := |mertensSecondConstant| + C₁ / log 2
  let C : ℝ := max (4 / (log 2) ^ (6 : ℝ)) (rexp (6 * K))
  have hlg2 : (0 : ℝ) < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hCpos : 0 < C := by
    dsimp [C]
    exact lt_max_of_lt_left (div_pos (by norm_num : (0 : ℝ) < 4) (Real.rpow_pos_of_pos hlg2 (6 : ℝ)))
  refine ⟨C, hCpos, ?_⟩
  intro Q
  by_cases hQ : Q ≤ 2
  · have hbnd : panMainTotientWeightedSum Q ≤ 4 := by
      calc
        panMainTotientWeightedSum Q ≤ panMainTotientWeightedSum 2 := panMainTotientWeightedSum_mono hQ
        _ ≤ ∏ p ∈ primesUpTo 2, (1 + (3 : ℝ) / ((p : ℝ) - 1)) := panMainTotientWeightedSum_le_prod_one_add 2
        _ = 4 := by
              have hP : primesUpTo 2 = ({2} : Finset ℕ) := by
                ext p
                constructor
                · intro hp
                  have hp_pr : p.Prime := (mem_primesUpTo.mp hp).1
                  have hp_le : p ≤ 2 := (mem_primesUpTo.mp hp).2
                  interval_cases p
                  · norm_num at hp_pr
                  · norm_num at hp_pr
                  · simp
                · intro hp
                  have hp2 : p = 2 := by simpa using hp
                  subst p
                  exact mem_primesUpTo.2 ⟨by norm_num, by norm_num⟩
              rw [hP]
              norm_num
    have hQ2 : (2 : ℕ) ≤ Q + 2 := by omega
    have hlgQ2nn : (0 : ℝ) ≤ Real.log (Q + 2) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Q + 2))
    have hlogle : (log 2) ^ (6 : ℝ) ≤ (Real.log (Q + 2)) ^ (6 : ℝ) := by
      exact Real.rpow_le_rpow (le_of_lt hlg2)
        (Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hQ2))
        (by norm_num : (0 : ℝ) ≤ (6 : ℝ))
    calc
      panMainTotientWeightedSum Q ≤ 4 := hbnd
      _ = 4 / (log 2) ^ (6 : ℝ) * (log 2) ^ (6 : ℝ) := by
        have hx : (log 2) ^ (6 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hlg2 (6 : ℝ)).ne'
        field_simp [hx]
      _ ≤ 4 / (log 2) ^ (6 : ℝ) * (Real.log (Q + 2)) ^ (6 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hlogle
          (div_nonneg (by norm_num : (0 : ℝ) ≤ 4) (le_of_lt (Real.rpow_pos_of_pos hlg2 (6 : ℝ))))
      _ ≤ C * (Real.log (Q + 2)) ^ (6 : ℝ) := by
        exact mul_le_mul_of_nonneg_right (le_max_left (4 / (log 2) ^ (6 : ℝ)) (rexp (6 * K)))
          (Real.rpow_nonneg hlgQ2nn (6 : ℝ))
  · have hQ3 : 3 ≤ Q := by omega
    have hQ2 : 2 ≤ Q := by omega
    have hQ1 : (1 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 1 < Q)
    have hlogQ : (0 : ℝ) < log (Q : ℝ) := Real.log_pos hQ1
    have hlogQnn : (0 : ℝ) ≤ log (Q : ℝ) := le_of_lt hlogQ
    have hM' : |primeReciprocalSum Q - (log (log (Q : ℝ)) + mertensSecondConstant)| ≤
        C₁ / log (Q : ℝ) := hM Q hQ2
    have hpRS : primeReciprocalSum Q ≤ log (log (Q : ℝ)) + K := by
      have hle1 : primeReciprocalSum Q ≤
          log (log (Q : ℝ)) + mertensSecondConstant + C₁ / log (Q : ℝ) := by
        linarith [(abs_le.mp hM').2]
      have hc : mertensSecondConstant ≤ |mertensSecondConstant| := le_abs_self _
      have hC : C₁ / log (Q : ℝ) ≤ C₁ / log 2 := by
        exact div_le_div_of_nonneg_left (le_of_lt hC₁) hlg2
          (Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hQ2))
      dsimp [K]
      linarith
    have hsum : (∑ p ∈ primesUpTo Q, (3 : ℝ) / ((p : ℝ) - 1)) ≤ 6 * primeReciprocalSum Q := by
      calc
        (∑ p ∈ primesUpTo Q, (3 : ℝ) / ((p : ℝ) - 1))
            ≤ ∑ p ∈ primesUpTo Q, (6 : ℝ) / (p : ℝ) := by
              apply Finset.sum_le_sum
              intro p hp
              have hp_pr : p.Prime := (mem_primesUpTo.mp hp).1
              have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_pr.two_le
              have hppos : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
              have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
              rw [div_le_div_iff₀ hpm1 hppos]
              nlinarith
        _ = 6 * (∑ p ∈ primesUpTo Q, 1 / (p : ℝ)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro p hp
              ring
        _ = 6 * primeReciprocalSum Q := by
              unfold primeReciprocalSum
              rfl
    have hlgQ2nn : (0 : ℝ) ≤ Real.log (Q + 2) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Q + 2))
    have hlogle : (log (Q : ℝ)) ^ (6 : ℝ) ≤ (Real.log (Q + 2)) ^ (6 : ℝ) := by
      exact Real.rpow_le_rpow hlogQnn
        (Real.log_le_log (by positivity : (0 : ℝ) < (Q : ℝ)) (by exact_mod_cast (by omega : Q ≤ Q + 2)))
        (by norm_num : (0 : ℝ) ≤ (6 : ℝ))
    let u : ℕ → ℝ := fun p => if 2 ≤ p then (3 : ℝ) / ((p : ℝ) - 1) else 0
    have hu_nonneg : ∀ p : ℕ, 0 ≤ u p := by
      intro p
      by_cases h : 2 ≤ p
      · have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
          have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast h
          linarith
        simp [u, h, div_nonneg (by norm_num : (0 : ℝ) ≤ 3) (le_of_lt hp1)]
      · simp [u, h]
    have hu_eq : ∀ p ∈ primesUpTo Q, u p = (3 : ℝ) / ((p : ℝ) - 1) := by
      intro p hp
      have hp2 : 2 ≤ p := (mem_primesUpTo.mp hp).1.two_le
      simp [u, hp2]
    have hsum_u : (∑ p ∈ primesUpTo Q, u p) = ∑ p ∈ primesUpTo Q, (3 : ℝ) / ((p : ℝ) - 1) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hu_eq p hp
    calc
      panMainTotientWeightedSum Q ≤ ∏ p ∈ primesUpTo Q, (1 + (3 : ℝ) / ((p : ℝ) - 1)) :=
            panMainTotientWeightedSum_le_prod_one_add Q
      _ = ∏ p ∈ primesUpTo Q, (1 + u p) := by
            apply Finset.prod_congr rfl
            intro p hp
            rw [hu_eq p hp]
      _ ≤ rexp (∑ p ∈ primesUpTo Q, u p) := by
            exact Real.prod_one_add_le_exp_sum (primesUpTo Q) hu_nonneg
      _ = rexp (∑ p ∈ primesUpTo Q, (3 : ℝ) / ((p : ℝ) - 1)) := by
            rw [hsum_u]
      _ ≤ rexp (6 * primeReciprocalSum Q) := by
            exact Real.exp_le_exp.mpr hsum
      _ ≤ rexp (6 * (log (log (Q : ℝ)) + K)) := by
            exact Real.exp_le_exp.mpr (by
              have h6 : (0 : ℝ) ≤ 6 := by norm_num
              exact mul_le_mul_of_nonneg_left hpRS h6)
      _ = rexp (6 * K) * (log (Q : ℝ)) ^ (6 : ℝ) := by
            have h1 : rexp (6 * (log (log (Q : ℝ)) + K)) =
                rexp (6 * K) * (log (Q : ℝ)) ^ (6 : ℝ) := by
              calc
                rexp (6 * (log (log (Q : ℝ)) + K)) = rexp (6 * log (log (Q : ℝ)) + 6 * K) := by
                  congr 1
                  ring
                _ = rexp (6 * log (log (Q : ℝ))) * rexp (6 * K) := by rw [Real.exp_add]
                _ = (log (Q : ℝ)) ^ (6 : ℝ) * rexp (6 * K) := by
                  have h2 : rexp (6 * log (log (Q : ℝ))) = (log (Q : ℝ)) ^ (6 : ℝ) := by
                    calc
                      rexp (6 * log (log (Q : ℝ))) = rexp (log (log (Q : ℝ)) * 6) := by
                        congr 1
                        ring
                      _ = rexp (log (log (Q : ℝ))) ^ (6 : ℝ) := by rw [Real.exp_mul]
                      _ = (log (Q : ℝ)) ^ (6 : ℝ) := by rw [Real.exp_log hlogQ]
                  rw [h2]
                _ = rexp (6 * K) * (log (Q : ℝ)) ^ (6 : ℝ) := by ring
            exact h1
      _ ≤ C * (Real.log (Q + 2)) ^ (6 : ℝ) := by
            exact mul_le_mul (le_max_right (4 / (log 2) ^ (6 : ℝ)) (rexp (6 * K))) hlogle
              (Real.rpow_nonneg hlogQnn (6 : ℝ)) (le_of_lt hCpos)


/-! ## 5. 诚实多对数版主项界 (中间证据)

对 `|f| ≤ 1`, 主项带权和 ≤ `C·|xX|·(1 + log X)·log⁶(Q+2)` — 全部来自
初等材料 (li 初等界 `|li(m)| ≤ m/log 2`, 调和级数, q 因子多对数界).
这是 `PanMainTermSieveBound` 目标的多对数中间证据; 吸收进
`C·xX·(log xX)^{A+7}` (固定多对数因子被更大的 log 幂次压制) 是
`PanMainSieveAbsorption` (§6, 已证明) 的解析内容. -/
theorem panMainWeightedSum_polylog (x : ℕ → ℝ) (f : ℕ → ℝ) (hfb : ∀ a : ℕ, |f a| ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ X Q : ℕ,
      (∑ q ∈ Finset.range (Q + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panPieceMaxY X q (Nat.floor (x X)) f
            (fun y q' l' => logarithmicIntegral (y : ℝ) / Nat.totient q')) ≤
        C * |x X| * (1 + Real.log (X : ℝ)) * (Real.log (Q + 2)) ^ (6 : ℝ) := by
  classical
  obtain ⟨C₁, hC₁, hQ⟩ := panMainTotientWeightedSum_le_polylog
  let C : ℝ := C₁ / log 2
  have hCpos : 0 < C := by
    dsimp [C]
    exact div_pos hC₁ (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  refine ⟨C, hCpos, ?_⟩
  intro X Q
  have hlogX : (0 : ℝ) ≤ 1 + Real.log (X : ℝ) := by
    by_cases hX : X = 0
    · subst X
      simp [Real.log_zero]
    · have hX1 : 1 ≤ X := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hX)
      have hlog : (0 : ℝ) ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX1)
      linarith
  have hfloor_abs : (Nat.floor (x X) : ℝ) ≤ |x X| := by
    by_cases hx : 0 ≤ x X
    · exact le_trans (Nat.floor_le hx) (le_abs_self (x X))
    · have hx' : x X < 1 := lt_trans (lt_of_not_ge hx) (by norm_num : (0 : ℝ) < 1)
      have hf : Nat.floor (x X) = 0 := Nat.floor_eq_zero.mpr hx'
      simp [hf]
  have hmain : mainTermInnerSumMax X (Nat.floor (x X)) ≤
      |x X| / log 2 * (1 + Real.log (X : ℝ)) := by
    calc
      mainTermInnerSumMax X (Nat.floor (x X)) ≤
          (Nat.floor (x X) : ℝ) / log 2 * (1 + Real.log (X : ℝ)) :=
        mainTermInnerSumMax_le X (Nat.floor (x X))
      _ ≤ |x X| / log 2 * (1 + Real.log (X : ℝ)) := by
        have hd : (Nat.floor (x X) : ℝ) / log 2 ≤ |x X| / log 2 :=
          div_le_div_of_nonneg_right hfloor_abs
            (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
        exact mul_le_mul_of_nonneg_right hd hlogX
  have hqnonneg : (0 : ℝ) ≤ C₁ * (Real.log (Q + 2)) ^ (6 : ℝ) := by
    have hlg : (0 : ℝ) ≤ Real.log (Q + 2) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Q + 2))
    exact mul_nonneg (le_of_lt hC₁) (Real.rpow_nonneg hlg (6 : ℝ))
  calc
    (∑ q ∈ Finset.range (Q + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panPieceMaxY X q (Nat.floor (x X)) f
            (fun y q' l' => logarithmicIntegral (y : ℝ) / Nat.totient q'))
        ≤ mainTermInnerSumMax X (Nat.floor (x X)) * panMainTotientWeightedSum Q := by
          simpa [panMainTotientWeightedSum] using
            panMainWeightedSum_le X Q (Nat.floor (x X)) f hfb
    _ ≤ mainTermInnerSumMax X (Nat.floor (x X)) * (C₁ * (Real.log (Q + 2)) ^ (6 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (hQ Q) (mainTermInnerSumMax_nonneg X (Nat.floor (x X)))
    _ ≤ (|x X| / log 2 * (1 + Real.log (X : ℝ))) * (C₁ * (Real.log (Q + 2)) ^ (6 : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hmain hqnonneg
    _ = C * |x X| * (1 + Real.log (X : ℝ)) * (Real.log (Q + 2)) ^ (6 : ℝ) := by
          dsimp [C]
          ring

/-! ## 6. 解析吸收台阶与 `PanMainTermSieveBound` 归约 -/

/-- **解析吸收台阶 (红队修正版, 已证明)**: `x` 是筛尺度, 假设筛尺度不小于
求和范围 (`X ≤ x X`; 典型实例 `x X = (X : ℝ)` 满足). 对该类 `x`, 固定多对数
因子 `(1 + log X)·log⁶(xX + 2)` 最终被任意更大的 log 幂次压制:

  `∀ A > 0, ∃ C > 0, x₀, ∀ X ≥ x₀:
     xX·(1 + log X)·log⁶(xX + 2) ≤ C·xX·(log xX)^{A+7}`.

**红队修正 (相对 line T3i / PR #41 的旧陈述)**: 旧陈述声称同样的多对数因子被
`C·xX/log^A(xX)` 压制 — 对任意满足 `1 < x X` 的 `x` **为假**:

  - `x X ≡ 2` (常数): 左侧含无界因子 `(1 + log X)`, 右侧为常数 — 假;
  - `x X = X` (典型实例): `(1 + log X)·log⁶(X+2) ≤ C/log^A(X)` 左侧
    ~ `log⁷X → ∞` 而右侧 `→ 0` — 对任意固定 `A, C` 最终假.

经典证明中 `li` 主项被筛主项 (`x/log x·∏(1-ν(p))`) **相减吸收**, 只余
`O(x/log^A x)` (Liu 2022 §III; HR 1974 Ch.10) — 那是 `PanMainTermBound`
级别的解析内容 (依赖筛积对象, 见 `PAN_PROOF_ATLAS.md` 红队注记与模块头),
不是单个不等式. 单个不等式能证明的只是: 固定多对数因子被**更大的** log 幂次
压制 (`≤ C·log^{A+7}`, 总度数 7). 定理 `panMainSieveAbsorption_of_dom`
(§6.1) 证明本陈述. -/
def PanMainSieveAbsorption (x : ℕ → ℝ) : Prop :=
  (∀ X : ℕ, (X : ℝ) ≤ x X) ∧
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℕ,
      ∀ X : ℕ, x₀ ≤ X →
        x X * (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ (6 : ℝ) ≤
          C * x X * (Real.log (x X)) ^ (A + 7)

/-! ## 6.1 解析吸收台阶的证明 (log 最终压制)

本节的解析内容: 对 `(X : ℝ) ≤ x X` 的筛尺度, 固定多对数因子
`(1 + log X)·log⁶(xX + 2)` 被任意更大的 log 幂次最终压制. 三步:

1. **log 最终下界** (`panMainSieve_log_ge_one`): `X ≤ xX` ⇒ `log X ≤ log(xX)`
   (log 单调), 而 `log X → ∞` (`Real.tendsto_log_atTop.comp`
   `tendsto_natCast_atTop_atTop`), 故最终 `1 ≤ log (x X)`;
2. **多对数乘积界** (`panMainSieve_polylog_le`, 自然幂): 对 `X ≥ 2` 与
   `1 ≤ log(xX)`: `log(xX+2) ≤ log(2·xX) = log 2 + log(xX) ≤ 2·log(xX)`
   (单调性 + `log 2 ≤ log(xX)`) 且 `1 + log X ≤ 1 + log(xX) ≤ 2·log(xX)`,
   故 `(1+log X)·log⁶(xX+2) ≤ (2L)·(2L)^6 = 128·log⁷(xX)` (总度数 7);
3. **更大幂次压制** (`panMainSieveAbsorption_of_dom`): 最终 `1 ≤ log(xX)` 时
   rpow 在底数 ≥ 1 处关于指数单调 (`Real.rpow_le_rpow_of_exponent_le`),
   `log⁷(xX) ≤ (log xX)^{A+7}` (`7 ≤ A+7` 来自 `0 < A`), 乘 `xX ≥ 0` 得目标.

全部是 mathlib 初等分析 (tendsto / rpow / log 单调), 零 sorry. -/

section PanMainSieveAbsorption_proof

open Filter

/-- **log 最终下界**: `(X : ℝ) ≤ x X` 时最终 `1 ≤ log (x X)`.
由 `log X → ∞` 与 `log X ≤ log(xX)` (log 单调 + `X ≤ xX`) 传递. -/
theorem panMainSieve_log_ge_one {x : ℕ → ℝ} (hdom : ∀ X : ℕ, (X : ℝ) ≤ x X) :
    ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (x X) := by
  have hlogX : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hge : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (X : ℝ) := hlogX (eventually_ge_atTop 1)
  filter_upwards [hge, eventually_ge_atTop (1 : ℕ)] with X h1 hX1
  have hX1r : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
  have hXpos : (0 : ℝ) < (X : ℝ) := lt_of_lt_of_le (by norm_num) hX1r
  exact le_trans h1 (Real.log_le_log hXpos (hdom X))

/-- **多对数乘积界 (核心, 自然幂)**: 对 `(X : ℝ) ≤ x X` 的筛尺度, 最终
`(1 + log X)·log⁶(xX+2) ≤ 128·log⁷(xX)`. 总度数 7: `1 + log X` 经
`1 ≤ log(xX)` 吸收进一个 log 因子 (≤ `2·log(xX)`), `log⁶(xX+2) ≤ (2·log(xX))^6`
(单调性 + `log(2·xX) = log 2 + log(xX)` + `log 2 ≤ log(xX)`). -/
theorem panMainSieve_polylog_le {x : ℕ → ℝ} (hdom : ∀ X : ℕ, (X : ℝ) ≤ x X) :
    ∀ᶠ X : ℕ in atTop,
      (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ 6 ≤
        128 * (Real.log (x X)) ^ 7 := by
  filter_upwards [panMainSieve_log_ge_one hdom, eventually_ge_atTop (1 : ℕ),
    eventually_ge_atTop (2 : ℕ)] with X hL hX1 hX2
  have hxXgeX : (X : ℝ) ≤ x X := hdom X
  have hX1r : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
  have hXpos : (0 : ℝ) < (X : ℝ) := lt_of_lt_of_le (by norm_num) hX1r
  have hxXpos : (0 : ℝ) < x X := lt_of_lt_of_le hXpos hxXgeX
  have hlogXle : Real.log (X : ℝ) ≤ Real.log (x X) := Real.log_le_log hXpos hxXgeX
  have h1add : 1 + Real.log (X : ℝ) ≤ 2 * Real.log (x X) := by nlinarith [hL, hlogXle]
  have hX2r : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
  have hxX2 : (2 : ℝ) ≤ x X := le_trans hX2r hxXgeX
  have hlogadd_le2 : Real.log (x X + 2) ≤ 2 * Real.log (x X) := by
    calc
      Real.log (x X + 2) ≤ Real.log (2 * x X) :=
        Real.log_le_log (by positivity : (0 : ℝ) < x X + 2) (by nlinarith [hxX2])
      _ = Real.log 2 + Real.log (x X) :=
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hxXpos)
      _ ≤ Real.log (x X) + Real.log (x X) := by
        have hlog2le : Real.log 2 ≤ Real.log (x X) :=
          Real.log_le_log (by norm_num : (0 : ℝ) < 2) hxX2
        linarith
      _ = 2 * Real.log (x X) := by ring
  have hlogadd_nn : (0 : ℝ) ≤ Real.log (x X + 2) := by
    have hlogadd_ge : Real.log (x X) ≤ Real.log (x X + 2) :=
      Real.log_le_log hxXpos (by nlinarith)
    linarith
  have hpow6 : (Real.log (x X + 2)) ^ 6 ≤ (2 * Real.log (x X)) ^ 6 :=
    pow_le_pow_left₀ hlogadd_nn hlogadd_le2 6
  have hb : (0 : ℝ) ≤ 2 * Real.log (x X) := by nlinarith [hL]
  calc
    (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ 6
        ≤ (2 * Real.log (x X)) * (2 * Real.log (x X)) ^ 6 := by
      exact mul_le_mul h1add hpow6 (pow_nonneg hlogadd_nn 6) hb
    _ = 128 * (Real.log (x X)) ^ 7 := by ring

/-- **`PanMainSieveAbsorption` 的证明**: 对满足 `X ≤ x X` 的筛尺度, 固定
多对数因子被任意更大的 log 幂次最终压制. 常数 `C = 128`; `x₀` 由最终性给出
(覆盖 `1 ≤ log(xX)` 与 `X ≥ 1`). 最后用 `eventually_atTop.mp` 把最终性
转成 `∃ x₀` 的显式形式. -/
theorem panMainSieveAbsorption_of_dom {x : ℕ → ℝ} (hdom : ∀ X : ℕ, (X : ℝ) ≤ x X) :
    PanMainSieveAbsorption x := by
  refine ⟨hdom, ?_⟩
  intro A hA
  refine ⟨128, by norm_num, ?_⟩
  have hpow7 : ∀ᶠ X : ℕ in atTop,
      (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ (6 : ℝ) ≤
        128 * (Real.log (x X)) ^ (A + 7) := by
    filter_upwards [panMainSieve_polylog_le hdom, panMainSieve_log_ge_one hdom] with X hprod hL
    calc
      (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ (6 : ℝ)
          ≤ (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ 6 := by
        have heq : (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ (6 : ℝ) =
            (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ 6 := by
          simpa using congrArg (fun t => (1 + Real.log (X : ℝ)) * t)
            (Real.rpow_natCast (Real.log (x X + 2)) 6)
        exact le_of_eq heq
      _ ≤ 128 * (Real.log (x X)) ^ 7 := hprod
      _ ≤ 128 * (Real.log (x X)) ^ (A + 7) := by
        have h7 : (Real.log (x X)) ^ 7 = (Real.log (x X)) ^ (7 : ℝ) := by
          simpa using (Real.rpow_natCast (Real.log (x X)) 7)
        have hle : (Real.log (x X)) ^ (7 : ℝ) ≤ (Real.log (x X)) ^ (A + 7) :=
          Real.rpow_le_rpow_of_exponent_le hL (by linarith : (7 : ℝ) ≤ A + 7)
        rw [h7]
        exact mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 128)
  have hev : ∀ᶠ X : ℕ in atTop,
      x X * (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ (6 : ℝ) ≤
        128 * x X * (Real.log (x X)) ^ (A + 7) := by
    filter_upwards [hpow7, eventually_ge_atTop (1 : ℕ)] with X hpowX hX1
    have hX0r : (0 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 0 ≤ X)
    have hxXnn : (0 : ℝ) ≤ x X := le_trans hX0r (hdom X)
    calc
      x X * (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ (6 : ℝ)
          = x X * ((1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ (6 : ℝ)) := by ring
      _ ≤ x X * (128 * (Real.log (x X)) ^ (A + 7)) := by
        exact mul_le_mul_of_nonneg_left hpowX hxXnn
      _ = 128 * x X * (Real.log (x X)) ^ (A + 7) := by ring
  exact eventually_atTop.mp hev

/-- **典型实例**: `x X = (X : ℝ)` 满足 `X ≤ x X` (定义性), 故
`PanMainSieveAbsorption (fun N : ℕ => (N : ℝ))`. -/
theorem panMainSieveAbsorption_natCast :
    PanMainSieveAbsorption (fun N : ℕ => (N : ℝ)) := by
  apply panMainSieveAbsorption_of_dom
  intro X
  rfl

end PanMainSieveAbsorption_proof

/-- **`PanMainTermSieveBound` 的归约**: 多对数吸收台阶 (`PanMainSieveAbsorption`,
已证明) ⇒ `PanMainTermSieveBound`. 全部有限部分 (li 初等界, 调和级数, q 因子
多对数界, floor/√ 归约, 权重非负) 在此证明; 解析输入是吸收本身. 注意 RHS 是
多对数形式 `C·xX·(log xX)^{A+7}` (红队修正, 见 §6 注记). -/
theorem PanMainTermSieveBound.of_innerSumBound {x : ℕ → ℝ} {f : ℕ → ℝ}
    (hfb : ∀ a : ℕ, |f a| ≤ 1) (hAbs : PanMainSieveAbsorption x) :
    PanMainTermSieveBound x f := by
  rcases hAbs with ⟨hdom, hAbs'⟩
  obtain ⟨C₁, hC₁, hQ⟩ := panMainTotientWeightedSum_le_polylog
  refine ⟨hfb, fun A hA => ?_⟩
  obtain ⟨C₂, hC₂, x₀, hAbsX⟩ := hAbs' A hA
  let C : ℝ := C₁ * C₂ / log 2
  have hCpos : 0 < C := by
    dsimp [C]
    exact div_pos (mul_pos hC₁ hC₂) (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  -- 吸收给出的 x₀ 之外再要求 X ≥ 1 (保证 xX ≥ X ≥ 1 > 0, 筛尺度正性).
  refine ⟨C, hCpos, (0 : ℝ), max x₀ 1, ?_⟩
  intro X hX
  have hX₀ : x₀ ≤ X := by omega
  have hX1 : 1 ≤ X := by omega
  let Q : ℕ := Nat.floor ((x X) ^ (1 / 2 : ℝ))
  have hQdef : Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ (0 : ℝ)) = Q := by
    simp [Q, Real.rpow_zero]
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlogX : (0 : ℝ) ≤ 1 + Real.log (X : ℝ) := by
    have hlog : (0 : ℝ) ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX1)
    linarith
  have hxXgeX : (X : ℝ) ≤ x X := hdom X
  have hX1r : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
  have hxXpos : (0 : ℝ) < x X :=
    lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hX1r) hxXgeX
  have hxXone : (1 : ℝ) ≤ x X := le_trans hX1r hxXgeX
  have hfloor : (Nat.floor (x X) : ℝ) ≤ x X := Nat.floor_le (le_of_lt hxXpos)
  have hsqrt : (x X) ^ (1 / 2 : ℝ) ≤ x X := by
    rw [← Real.sqrt_eq_rpow]
    calc
      √(x X) ≤ √((x X) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [hxXone] : (x X : ℝ) ≤ (x X) ^ 2)
      _ = x X := Real.sqrt_sq (le_of_lt hxXpos)
  have hQle : (Q : ℝ) ≤ x X := by
    dsimp [Q]
    exact le_trans (Nat.floor_le (Real.rpow_nonneg (le_of_lt hxXpos) (1 / 2 : ℝ))) hsqrt
  have hQlog : Real.log (Q + 2) ≤ Real.log (x X + 2) := by
    have hpos : (0 : ℝ) < (Q : ℝ) + 2 := by positivity
    have hle : ((Q + 2 : ℕ) : ℝ) ≤ x X + 2 := by
      norm_num [Nat.cast_add]
      exact hQle
    exact Real.log_le_log hpos (by simpa [Nat.cast_add] using hle)
  have hlogle : (Real.log (Q + 2)) ^ (6 : ℝ) ≤ (Real.log (x X + 2)) ^ (6 : ℝ) := by
    have hlognn : (0 : ℝ) ≤ Real.log (Q + 2) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Q + 2))
    exact Real.rpow_le_rpow hlognn hQlog (by norm_num : (0 : ℝ) ≤ (6 : ℝ))
  have hmain : mainTermInnerSumMax X (Nat.floor (x X)) ≤
      x X / log 2 * (1 + Real.log (X : ℝ)) := by
    calc
      mainTermInnerSumMax X (Nat.floor (x X)) ≤
          (Nat.floor (x X) : ℝ) / log 2 * (1 + Real.log (X : ℝ)) :=
        mainTermInnerSumMax_le X (Nat.floor (x X))
      _ ≤ x X / log 2 * (1 + Real.log (X : ℝ)) := by
        have hd : (Nat.floor (x X) : ℝ) / log 2 ≤ x X / log 2 :=
          div_le_div_of_nonneg_right hfloor (le_of_lt hlog2)
        exact mul_le_mul_of_nonneg_right hd hlogX
  calc
    mainTermInnerSumMax X (Nat.floor (x X)) *
        (∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ (0 : ℝ)) + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ))
        = mainTermInnerSumMax X (Nat.floor (x X)) * panMainTotientWeightedSum Q := by
          rw [hQdef]
          rfl
    _ ≤ mainTermInnerSumMax X (Nat.floor (x X)) * (C₁ * (Real.log (Q + 2)) ^ (6 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (hQ Q) (mainTermInnerSumMax_nonneg X (Nat.floor (x X)))
    _ ≤ (x X / log 2 * (1 + Real.log (X : ℝ))) * (C₁ * (Real.log (Q + 2)) ^ (6 : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hmain (by
            have hlg : (0 : ℝ) ≤ Real.log (Q + 2) :=
              Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Q + 2))
            exact mul_nonneg (le_of_lt hC₁) (Real.rpow_nonneg hlg (6 : ℝ)))
    _ ≤ (x X / log 2 * (1 + Real.log (X : ℝ))) * (C₁ * (Real.log (x X + 2)) ^ (6 : ℝ)) := by
          have hcl : C₁ * (Real.log (Q + 2)) ^ (6 : ℝ) ≤
              C₁ * (Real.log (x X + 2)) ^ (6 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hlogle (le_of_lt hC₁)
          exact mul_le_mul_of_nonneg_left hcl (by
            have hnn : (0 : ℝ) ≤ x X / log 2 * (1 + Real.log (X : ℝ)) :=
              mul_nonneg (div_nonneg (le_of_lt hxXpos) (le_of_lt hlog2)) hlogX
            exact hnn)
    _ = (C₁ / log 2) * (x X * (1 + Real.log (X : ℝ)) * (Real.log (x X + 2)) ^ (6 : ℝ)) := by
          ring
    _ ≤ (C₁ / log 2) * (C₂ * x X * (Real.log (x X)) ^ (A + 7)) := by
          exact mul_le_mul_of_nonneg_left (hAbsX X hX₀) (le_of_lt (div_pos hC₁ hlog2))
    _ = C * x X * (Real.log (x X)) ^ (A + 7) := by
          dsimp [C]
          ring

end AnalyticNumberTheory.Sieve
