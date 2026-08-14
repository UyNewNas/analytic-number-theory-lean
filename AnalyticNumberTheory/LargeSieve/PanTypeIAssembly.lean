/-
! # AnalyticNumberTheory.LargeSieve.PanTypeIAssembly

## S2--S4: 原特征 → 全特征重组, 闭合 panTypeICharMeanSieveBound (issue #42)

本模块把已证的**原特征** Bombieri--Davenport 大筛均值
(`bombieriDavenport_vaughanFirst`, BombieriDavenport.lean) 装配到
`panTypeICharMeanSieveBound` 的**全特征 + 权重**形式, 并按红队审查
把不可证的部分拆成显式 Prop 子台阶 (S2--S4). 已证材料:

- `bombieriDavenport_vaughanFirst (Q m u) (hQ : 0 < Q)`:
  `Σ_{1≤q≤Q} (q/φ(q))·Σ_{χ 原特征 mod q} ‖V_χ(m)‖² ≤ LSB(m+1, 1/Q²)·S(m)`,
  `S(m) = Σ_{n≤m} vaughanFirst(n,u)²` (原特征, 已证).
- `panTypeICharSqSum_le_additiveSieve q m u hq`: 逐 q 全特征
  `t_q(m) := Σ_{χ mod q} ‖V_χ(m)‖² ≤ (φ(q)/q)·LSB(m+1, 1/q²)·S(m)` (已证).
- `panTypeI_charAbsSum_le_cs` (CS 块): `Σ_χ‖V_χ‖ ≤ √φ(q)·√(t_q(m))` (已证).
- `panTypeICharSqrtMeanMaxY_le_sieveSqrtSum` (深化归约, 已证):
  `panTypeICharSqrtMeanMaxY X q x f u ≤ Σ_{y≤x}Σ_{a≤X} |f(a)|/|log(y/a)|·√((φ/q)·LSB(y/a+1,1/q²))·√S(y/a)`.

目标 (`PanMeanValueBody.lean`):
`panTypeICharMeanSieveBound x f u`:
`Σ_{q≤Q} μ²(q)3^{ω(q)}·√φ(q)·panTypeICharSqrtMeanMaxY X q (xX) f u ≤ C·xX/log^A(xX)`,
`Q = (xX)^{1/2}/log^B(xX)`.

---

## 红队修正: panTypeICharMeanSieveBound 对 |f| ≤ 1 一致为假

目标对**全体** `|f| ≤ 1` 一致 (`(∀ a, |f a| ≤ 1)`). 取 `u = 1`
(`vaughanFirst(n,1) = log n`), `f = 1_{a = 1}` (`f(1) = 1`, 其余为 0),
`y = xX`, `a = 1`. 主特征 `χ₀ mod q` 项 (含于 `t_q`):
`‖V_{χ₀}(xX)‖ = Σ_{n≤xX, (n,q)=1} log n ~ (φ(q)/q)·xX·log(xX)` (初等密度, 无需 PNT).
于是 (max_y ≥ y = xX 项, 各项非负):

```text
LHS ≥ (1/log(xX))·Σ_{q≤Q} μ²(q)3^{ω(q)}·√φ(q)·‖V_{χ₀}(xX)‖
    ~ xX·Σ_{q≤Q} μ²(q)3^{ω(q)}·φ(q)^{3/2}/q
    ≥ xX·Σ_{p≤Q, p prime} 3·(p−1)^{3/2}/p  ~  (2/3)·xX·Q^{3/2}/log Q
    = (2/3)·(xX)^{7/4}/(log xX)^{1+3B/2},
```

对任意固定 `A, B, C` 与充分大的 `xX` 超过 `C·xX/log^A(xX)`. 故
`panTypeICharMeanSieveBound` (|f| ≤ 1 一致) **为假**. 经典 type I 均值定理
(Liu 2022 §III Lemma 1; HR 1974 Ch.10) 的 `f` 有支撑条件 (Chen 权重
`f(a) = 1_{a = p₁p₂, z ≤ p₁ ≤ p₂}`: `f(1) = 0` 且 `Σ_{a≤X}|f(a)|/a`
可控). 修正输入 `panTypeI_charMeanSieveBound_chenWeight` 见 §S4.

---

## S2: 原特征分解 (conductor decomposition) — 需新特征理论, 拆为显式子台阶

对 `χ mod q`, 令 `q' = χ.conductor` (mathlib: `χ.conductor : ℕ`,
`χ.FactorsThrough q'`, `χ'.IsPrimitive`), `q' | q`, `χ'` 为唯一原特征.
诱导关系: `χ(n) = χ'(n mod q')` 当 `(n, q) = 1`, 否则 `χ(n) = 0`
(mathlib 约定非互素值为 0). 于是

```text
V_χ(m) = Σ_{n≤m, (n,q)=1} vaughanFirst(n,u)·χ'(n mod q'),
‖V_χ(m)‖ ≤ ‖V_χ'(m)‖ + D_q(m),   D_q(m) = Σ_{n≤m, (n,q)>1} |vaughanFirst(n,u)|,
‖V_χ(m)‖² ≤ 2‖V_χ'(m)‖² + 2·D_q(m)²,
```

分组 (原特征部分 = χ' 的模 q 特征个数 ≤ φ(q)/φ(q')):

```text
t_q(m) ≤ 2·Σ_{q'|q} (φ(q)/φ(q'))·P_{q'}(m) + 2·φ(q)·D_q(m)²,   P_{q'}(m) = Σ_{χ' 原特征 mod q'} ‖V_χ'(m)‖².
```

**评估**: mathlib 提供 conductor/FactorsThrough/IsPrimitive (本仓库
`star_conductor`/`star_isPrimitive` 已用), 但 (i) 诱导关系的逐点分解引理
(χ(n) = χ'(n mod q')), (ii) 按原特征部分的分组双射与计数 φ(q)/φ(q'), (iii)
非互素项密度估计, 都是**新特征理论/初等数论**, 不在现有材料中. 显式子台阶:

- S2a `panTypeI_char_induced_by_primitive`: 诱导特征逐点分解.
- S2b `panTypeI_sqSum_primitiveDecomposition`: 上述平方和分解 (含密度因子).
- S2c `panTypeI_nonCoprimeDensity_le`: `D_q(m)` 的密度估计 (路线:
  `D_q(m) ≤ Σ_{p|q} Σ_{n≤m, p|n} |vaughanFirst(n,u)|`, 代入 `n = p·k` 用
  `vaughanFirst_abs_le` (`|vaughanFirst(n,u)| ≤ τ(n)·log(n+1)`, 已证)
  与除数密度 `Σ_{k≤m/p} τ(pk)·log(pk+1) ≤ C·(1/p)·m·log²(m+2)·polylog(p)`).

---

## S3: μ²3^ω 权重装配 — 部分可证

需要的初等估计 (polylog 吸收进常数):

```text
(W1) Σ_{q≤Q} μ²(q)3^{ω(q)}·φ(q)/q  ≤ C·Q·log⁶(Q+2)   [φ(q)/q ≤ 1 + Σ μ²3^ω ≤ C·Q·log³]
(W2) Σ_{k≤Q/q'} μ²(q'k)3^{ω(q'k)}·(q'k) ≤ C·(Q²/q')·3^{ω(q')}·log⁶(Q+2)
     [q = q'·k, μ²(q'k) ≤ μ²(k), 3^{ω(q'k)} ≤ 3^{ω(q')}·3^{ω(k)}, Σ_{k≤K} μ²3^ω·k ≤ C·K²·log³]
(W3) Σ_{q≤Q} μ²(q)3^{ω(q)}/φ(q) ≤ C·log⁶(Q+2)   [已证: panMainTotientWeightedSum_le_polylog]
```

(W1)/(W2) 的证明装置与 PanMainTerm.lean §4 相同 (子集展开 +
`sum_squarefree_prod_primeFactors_le_prod_one_add` + Mertens 第二定理
`mertensSecond_nat`); (W3) 由 `panTypeI_totientWeightSum_polylog` (本文件
重述, 已证) 给出.

---

## S4: sqrt 归约与装配 — 代数块已证, 装配开放

(1) **CS-in-q 代数块 (已证)**: `csSqrtSum_le_card_mul_sum`:
`(Σ_i √(a_i·b_i))² ≤ (card s)·Σ_i a_i·b_i` (`a_i·b_i ≥ 0`). 取
`a_q = w_q·φ(q)/q`, `b_q = w_q·q·t_q(m)` (`w_q = μ²3^ω`) 得
`(Σ_q w_q·√(φ(q)·t_q(m)))² ≤ (card)·Σ_q w_q²·φ(q)·t_q(m)`, 即 CS-in-q
把 `√φ(q)` 权重归约到 `Σ_q (φ(q)/q)` 与 `Σ_q q·t_q(m)` 两个因子
(`q·t_q(m) ≤ Q·(q/φ(q))·t_q(m)`, q ≤ Q, φ(q) ≤ q).

(2) **全特征 BD 均值输入 (开放, S4b)**: `panTypeI_allCharSieveMean`:
`Σ_{q≤Q} μ²3^ω·(q/φ(q))·t_q(m) ≤ C·(m+Q²)·S(m)·log⁶(Q+2)`. 路线:
S2 分解 → q-求和换序 (q = q'·k) → 对 `P_{q'}(m)` 用
`bombieriDavenport_vaughanFirst` (q' ≤ Q, LSB(m+1, 1/Q²) ~ m + Q²·log Q,
弱常数依赖见 BombieriDavenport.lean 尾部 S4 注记) → 非互素项经 S2c 吸收.
注意: 换序中的权重传递 `Σ_{q'|q}(φ(q)/φ(q'))·(q/φ(q)) = q/φ(q')` 与
(W2) 的 `Q²/q'` 因子使朴素装配多出 `Q²` 因子 — 经典证明中该因子被
`(q'/φ(q'))`-加权 BD 与 (W1)/(W3) 的精确簿记吸收 (polylog 吸收进 C),
精确簿记是 S3 的研究内容.

(3) **外层 (y,a) 权重和 (开放)**: 经 `panTypeICharSqrtMeanMaxY_le_sieveSqrtSum`
去 max 后, 剩余 `Σ_{y,a} |f(a)|/|log(y/a)|·(φ(q)/√q)·√LSB·√S` 型的 (y,a)
双重和; 对 Chen 权重 `Σ_{a≤X}|f(a)|/a` 可控性是该和收敛的关键 (|f| ≤ 1
一致形式由上述反例排除). 经典引用: Liu 2022 §III Lemma 1; HR 1974 Ch.10.

**诚实状态**: 本文件零 sorry; 已证 = CS 代数块 + W3 锚点; S2a--S2c, W1, W2,
S4b, 以及修正输入 `panTypeI_charMeanSieveBound_chenWeight` 为显式开放子台阶
(数学路线如上).
-/

import AnalyticNumberTheory.LargeSieve.BombieriDavenport
import AnalyticNumberTheory.Sieve.PanMainTerm
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

namespace AnalyticNumberTheory.LargeSieve

open Finset
open scoped BigOperators
open Classical
open AnalyticNumberTheory.Sieve
open scoped ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

/-! ## S3 锚点: 已证的权重 φ-和 -/

/-- **W3 (已证, 重述自 PanMainTerm)**: `Σ_{q≤Q} μ²(q)·3^{ω(q)}/φ(q) ≤ C·log⁶(Q+2)`.
  这是 S3 权重装配的一个因子 (PanMainTerm.lean §4 已证). -/
theorem panTypeI_totientWeightSum_polylog :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ,
      (∑ q ∈ Finset.range (Q + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) ≤
        C * (Real.log (Q + 2)) ^ (6 : ℝ) := by
  simpa [panMainTotientWeightedSum] using panMainTotientWeightedSum_le_polylog

/-! ## S2: 原特征分解 (conductor decomposition) — 显式开放子台阶 -/

/-- **S2a (开放)**: 每个特征 `χ mod q` 由唯一原特征 `χ' mod q'` (`q' | q`)
  诱导: 对 `(n, q) = 1` 有 `χ(n mod q) = χ'(n mod q')` (非互素处 mathlib
  约定为 0). 数学路线: mathlib `χ.FactorsThrough χ.conductor`
  (`DirichletCharacter.factorsThrough_conductor`) 给出通过 `q'` 的因子分解;
  需要新引理把该因子分解翻译为逐点取值等式 (既有用法见
  `BombieriDavenport.star_conductor`/`star_isPrimitive`). -/
def panTypeI_char_induced_by_primitive (q : ℕ) : Prop :=
  ∀ χ : DirichletCharacter ℂ q, ∃ q' : ℕ, q' ∣ q ∧
    ∃ χ' : DirichletCharacter ℂ q', χ'.IsPrimitive ∧
      ∀ n : ℕ, n.Coprime q → χ (n : ZMod q) = χ' (n : ZMod q')

/-- 非互素密度项: `D_q(m) = Σ_{n ≤ m, (n,q) > 1} |vaughanFirst(n,u)|`. -/
noncomputable def panTypeI_nonCoprimeDensity (q m u : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (m + 1), if (n.gcd q) ≠ 1 then |vaughanFirst n u| else 0

/-- **S2b (开放)**: 全特征平方和的原特征分解 (带密度因子):
  `t_q(m) ≤ 2·Σ_{q' | q} (φ(q)/φ(q'))·P_{q'}(m) + 2·φ(q)·D_q(m)²`,
  其中 `P_{q'}(m) = Σ_{χ' 原特征 mod q'} ‖V_χ'(m)‖²`. 数学路线:
  (i) S2a 诱导分解 ⟹ `‖V_χ(m)‖ ≤ ‖V_χ'(m)‖ + D_q(m)` (|χ'| ≤ 1) ⟹
  `‖V_χ‖² ≤ 2‖V_χ'‖² + 2·D_q²`;
  (ii) 按原特征部分分组: 每组 `χ' mod q'` 对应至多 `φ(q)/φ(q')` 个模 q
  特征 (conductor 整除 q' 的特征数为 `φ(q)/φ(q')`, 核 `ker((Z/qZ)^× → (Z/q'Z)^×)`
  的字符群). 需要新特征理论: 分组双射与计数. -/
def panTypeI_sqSum_primitiveDecomposition (q m u : ℕ) : Prop :=
  panTypeICharSqSum q m u ≤
    2 * (∑ q' ∈ q.divisors,
          ((Nat.totient q : ℝ) / (Nat.totient q' : ℝ)) *
            (∑ χ' ∈ (Finset.univ : Finset (DirichletCharacter ℂ q')).filter (fun χ' => χ'.IsPrimitive),
              ‖panTypeIV1CharSum q' m u χ'‖ ^ 2)) +
    2 * (Nat.totient q : ℝ) * (panTypeI_nonCoprimeDensity q m u) ^ 2

/-- **S2c (开放)**: 非互素密度项的密度估计:
  `D_q(m) ≤ C·(Σ_{p | q} 1/p)·Σ_{n ≤ m} |vaughanFirst(n,u)|`.
  数学路线: `(n,q) > 1` ⟹ 存在 `p | q`, `p | n`; 代入 `n = p·k` 后
  用已证点式界 `vaughanFirst_abs_le` (`|vaughanFirst(n,u)| ≤ τ(n)·log(n+1)`)
  与除数函数在倍数上的密度 `Σ_{k ≤ m/p} τ(pk)·log(pk+1) ≤ C·(1/p)·m·log²(m+2)·log p`
  (初等, 需要 divisor-count 在算术级数上的界; 开放). -/
def panTypeI_nonCoprimeDensity_le (q m u : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    panTypeI_nonCoprimeDensity q m u ≤
      C * (∑ p ∈ q.primeFactors, (1 : ℝ) / (p : ℝ)) *
        (∑ n ∈ Finset.range (m + 1), |vaughanFirst n u|)

/-! ## S3: μ²3^ω 权重估计 — 显式开放子台阶 -/

/-- **S3 (开放)**: 权重装配需要的初等估计族 (polylog 吸收进常数):
  (W1) `Σ_{q≤Q} μ²(q)3^{ω(q)}·φ(q)/q ≤ C·Q·log⁶(Q+2)`
  (`φ(q)/q ≤ 1` + `Σ_{q≤Q} μ²3^ω ≤ C·Q·log³(Q+2)`, 后者与 PanMainTerm §4
  相同装置: 子集展开 + `sum_squarefree_prod_primeFactors_le_prod_one_add` +
  Mertens 第二定理);
  (W2) 传递权重 `Σ_{k ≤ Q/q'} μ²(q'k)3^{ω(q'k)}·(q'k) ≤ C·(Q²/q')·3^{ω(q')}·log⁶(Q+2)`
  (q = q'·k 换序, `μ²(q'k) ≤ μ²(k)`, `3^{ω(q'k)} ≤ 3^{ω(q')}·3^{ω(k)}`);
  (W3) `Σ_{q≤Q} μ²(q)3^{ω(q)}/φ(q) ≤ C·log⁶(Q+2)` — 已证
  (`panTypeI_totientWeightSum_polylog`). -/
def panTypeI_threeOmegaWeightSums (Q : ℕ) : Prop :=
  (∃ C : ℝ, 0 < C ∧
    (∑ q ∈ Finset.range (Q + 1),
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
        ((Nat.totient q : ℝ) / (q : ℝ))) ≤
      C * (Q : ℝ) * (Real.log (Q + 2)) ^ (6 : ℝ)) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ q' : ℕ, 1 ≤ q' →
    (∑ k ∈ Finset.Icc 1 (Q / q'),
      ((μ (q' * k) : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ (q' * k).primeFactors.card *
        (q' * k : ℝ)) ≤
      C * ((Q : ℝ) ^ 2 / (q' : ℝ)) * (3 : ℝ) ^ q'.primeFactors.card *
        (Real.log (Q + 2)) ^ (6 : ℝ)) ∧
  (∃ C : ℝ, 0 < C ∧
    (∑ q ∈ Finset.range (Q + 1),
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) ≤
      C * (Real.log (Q + 2)) ^ (6 : ℝ))

/-! ## S4: sqrt 归约 (CS 块, 已证) 与装配输入 (开放) -/

/-- **S4a (已证, CS-in-√ 代数块)**: `(Σ_i √(a_i·b_i))² ≤ (card s)·Σ_i a_i·b_i`
  当 `a_i·b_i ≥ 0`. 由 `sq_sum_le_card_mul_sum_sq` (Chebyshev) 与
  `Real.sq_sqrt` 给出. BD 均值装配中取 `a_q = w_q·φ(q)/q`,
  `b_q = w_q·q·t_q(m)` 即得 `(Σ_q w_q·√(φ(q)·t_q(m)))² ≤
  (card)·Σ_q w_q²·φ(q)·t_q(m)` (CS-in-q 的代数内容). -/
theorem csSqrtSum_le_card_mul_sum {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (h : ∀ i ∈ s, 0 ≤ a i * b i) :
    (∑ i ∈ s, Real.sqrt (a i * b i)) ^ 2 ≤ (s.card : ℝ) * (∑ i ∈ s, a i * b i) := by
  calc
    (∑ i ∈ s, Real.sqrt (a i * b i)) ^ 2
        ≤ (s.card : ℝ) * (∑ i ∈ s, (Real.sqrt (a i * b i)) ^ 2) := by
          simpa using (sq_sum_le_card_mul_sum_sq (s := s)
            (f := fun i => Real.sqrt (a i * b i)))
    _ = (s.card : ℝ) * (∑ i ∈ s, a i * b i) := by
          congr 1
          exact Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (h i hi))

/-- **S4b (开放)**: 全特征加权 BD 均值输入 (S2 + S3 + 已证原特征 BD 的输出):
  `Σ_{1≤q≤Q} μ²(q)3^{ω(q)}·(q/φ(q))·t_q(m) ≤ C·(m+Q²)·S(m)·log⁶(Q+2)`.
  数学路线: (i) S2b 分解 `t_q(m)`; (ii) q-求和换序 (q = q'·k, (W2) 传递
  权重 `Σ_{q'|q} (φ(q)/φ(q'))·(q/φ(q)) = q/φ(q')`); (iii) 对 `P_{q'}(m)`
  应用 `bombieriDavenport_vaughanFirst` (q' ≤ Q, `LSB(m+1, 1/Q²) ~
  m + Q²·log Q` 弱常数, 见 BombieriDavenport.lean 尾部); (iv) 非互素项经
  S2c 吸收. 注意朴素换序的 `Q²/q'` 因子 (见模块头) — 精确簿记是 S3 的研究内容. -/
def panTypeI_allCharSieveMean (Q m u : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    (∑ q ∈ Finset.Icc 1 Q,
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
        ((q : ℝ) / (Nat.totient q : ℝ)) * panTypeICharSqSum q m u) ≤
      C * ((m : ℝ) + (Q : ℝ) ^ 2) *
        (∑ n ∈ Finset.range (m + 1), (vaughanFirst n u) ^ 2) *
        (Real.log (Q + 2)) ^ (6 : ℝ)

/-- **红队修正后的 T1' 输入 (开放, 暂定形式)**: 经典 type I 均值定理
  (Liu 2022 §III Lemma 1; HR 1974 Ch.10) 的 `f` 有支撑条件 (Chen 权重:
  `f(1) = 0` 且 `Σ_{a≤X} |f(a)|/a` 可控). 对 |f| ≤ 1 一致的
  `panTypeICharMeanSieveBound` 为假 (模块头反例). 本定义把支撑条件显式化;
  精确条件需对照经典源核实 (暂定). -/
def panTypeI_charMeanSieveBound_chenWeight (x : ℕ → ℝ) (f : ℕ → ℝ) (u : ℕ) : Prop :=
  (∀ a : ℕ, |f a| ≤ 1) ∧ (f 1 = 0) ∧
    (∃ C₀ : ℝ, 0 < C₀ ∧ ∀ X : ℕ,
      (∑ a ∈ Finset.Icc 1 X, |f a| / (a : ℝ)) ≤ C₀ * (Real.log (X + 2)) ^ (2 : ℝ)) ∧
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
      ∀ X : ℕ, x₀ ≤ X →
        ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B) + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            Real.sqrt (Nat.totient q : ℝ) * panTypeICharSqrtMeanMaxY X q (Nat.floor (x X)) f u ≤
          C * x X / (Real.log (x X)) ^ A
