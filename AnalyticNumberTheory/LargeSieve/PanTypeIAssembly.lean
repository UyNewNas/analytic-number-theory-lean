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
open DirichletCharacter
open scoped ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 40000000

/-! ## S3 锚点: 已证的权重 φ-和 -/

/-- **W3 (已证, 重述自 PanMainTerm)**: `Σ_{q≤Q} μ²(q)·3^{ω(q)}/φ(q) ≤ C·log⁶(Q+2)`.
  这是 S3 权重装配的一个因子 (PanMainTerm.lean §4 已证). -/
theorem panTypeI_totientWeightSum_polylog :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ,
      (∑ q ∈ Finset.range (Q + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card / (Nat.totient q : ℝ)) ≤
        C * (Real.log (Q + 2)) ^ (6 : ℝ) := by
  simpa [panMainTotientWeightedSum] using panMainTotientWeightedSum_le_polylog

/-! ## S2: 原特征分解 (conductor decomposition) — S2a/S2b/S2c-结构 已证 -/

/-! ### S2a: 逐点诱导分解 (已证, mathlib `primitiveCharacter` 装置)

mathlib 已提供完整装置: `χ.primitiveCharacter` (层数 `χ.conductor` 的原特征),
`changeLevel_primitiveCharacter` (`χ = changeLevel χ.conductor_dvd_level χ.primitiveCharacter`),
`primitiveCharacter_isPrimitive`, `primitiveCharacter_apply_of_isCoprime`
(`(a,q)=1 ⟹ χ.primitiveCharacter a = χ a`). S2a 由此直接给出. -/

/-- **S2a 点式 (已证)**: `(n, q) = 1` 时 `χ(n mod q) = χ.primitiveCharacter(n mod χ.conductor)`. -/
lemma dirichletChar_eq_primitiveCharacter_of_coprime {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {n : ℕ} (hcop : n.Coprime q) :
    χ (n : ZMod q) = χ.primitiveCharacter (n : ZMod χ.conductor) := by
  simpa using
    (χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ))
      (Nat.isCoprime_iff_coprime.mpr hcop)).symm

/-- |χ(a)| ≤ 1 (单位: 模 1; 非单位: 0). -/
lemma dirichletChar_norm_le_one (q : ℕ) (χ : DirichletCharacter ℂ q) (a : ZMod q) : ‖χ a‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · rw [dirichletChar_norm_unit χ ha]
  · have hz : χ a = 0 := MulChar.map_nonunit χ ha
    rw [hz]
    norm_num

/-- **S2a (已证)**: 每个特征 `χ mod q` 由唯一原特征 `χ.primitiveCharacter mod χ.conductor`
  诱导 (唯一性: changeLevel 单射); 逐点等式对 `(n,q)=1` 成立, 非互素处 MulChar 约定值为 0. -/
theorem panTypeI_char_induced_by_primitive (q : ℕ) [NeZero q] :
    ∀ χ : DirichletCharacter ℂ q, ∃ q' : ℕ, q' ∣ q ∧
      ∃ χ' : DirichletCharacter ℂ q', χ'.IsPrimitive ∧
        ∀ n : ℕ, n.Coprime q → χ (n : ZMod q) = χ' (n : ZMod q') := by
  intro χ
  refine ⟨χ.conductor, χ.conductor_dvd_level, χ.primitiveCharacter,
    χ.primitiveCharacter_isPrimitive, ?_⟩
  intro n hn
  exact dirichletChar_eq_primitiveCharacter_of_coprime χ hn

/-! ### S2 平方和分解的逐点组件 (已证) -/

/-- V_χ(m) 的互素分解: 非互素项为 0. -/
lemma panTypeIV1CharSum_eq_coprimePart {q m u : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    panTypeIV1CharSum q m u χ =
      ∑ n ∈ Finset.range (m + 1),
        (if n.Coprime q then (vaughanFirst n u : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor)
         else 0) := by
  unfold panTypeIV1CharSum
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hc : n.Coprime q
  · simp [hc, dirichletChar_eq_primitiveCharacter_of_coprime χ hc]
  · have hnu : ¬ IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).not.mpr hc
    have hz : χ (n : ZMod q) = 0 := MulChar.map_nonunit χ hnu
    simp [hc, hz]

/-- 非互素密度项: `D_q(m) = Σ_{n ≤ m, (n,q) > 1} |vaughanFirst(n,u)|`. -/
noncomputable def panTypeI_nonCoprimeDensity (q m u : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (m + 1), if (n.gcd q) ≠ 1 then |vaughanFirst n u| else 0

/-- 非互素密度项非负. -/
lemma panTypeI_nonCoprimeDensity_nonneg (q m u : ℕ) : 0 ≤ panTypeI_nonCoprimeDensity q m u := by
  unfold panTypeI_nonCoprimeDensity
  exact Finset.sum_nonneg (fun n hn => by
    by_cases hc : (n.gcd q) ≠ 1 <;> simp [hc, abs_nonneg])

/-- **S2 关键点式界 (已证)**: `‖V_χ(m)‖ ≤ ‖V_{χ.primitiveCharacter}(m)‖ + D_q(m)`. -/
lemma panTypeIV1CharSum_norm_le_primitive {q m u : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ‖panTypeIV1CharSum q m u χ‖ ≤
      ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ +
        panTypeI_nonCoprimeDensity q m u := by
  let ψ := χ.primitiveCharacter
  let S_not : ℂ :=
    ∑ n ∈ Finset.range (m + 1),
      if ¬ n.Coprime q then (vaughanFirst n u : ℂ) * ψ (n : ZMod χ.conductor) else 0
  have hdiff : panTypeIV1CharSum q m u χ - panTypeIV1CharSum χ.conductor m u ψ = -S_not := by
    unfold panTypeIV1CharSum S_not ψ
    rw [← Finset.sum_sub_distrib]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : n.Coprime q
    · simp [hc, dirichletChar_eq_primitiveCharacter_of_coprime χ hc]
    · have hnu : ¬ IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).not.mpr hc
      have hz : χ (n : ZMod q) = 0 := MulChar.map_nonunit χ hnu
      simp [hc, hz]
  have hnorm1 : ‖panTypeIV1CharSum q m u χ‖ ≤
      ‖panTypeIV1CharSum χ.conductor m u ψ‖ + ‖S_not‖ := by
    calc
      ‖panTypeIV1CharSum q m u χ‖
          = ‖panTypeIV1CharSum χ.conductor m u ψ +
              (panTypeIV1CharSum q m u χ - panTypeIV1CharSum χ.conductor m u ψ)‖ := by
              congr 1
              abel
      _ ≤ ‖panTypeIV1CharSum χ.conductor m u ψ‖ +
            ‖panTypeIV1CharSum q m u χ - panTypeIV1CharSum χ.conductor m u ψ‖ := by
            exact norm_add_le _ _
      _ = ‖panTypeIV1CharSum χ.conductor m u ψ‖ + ‖S_not‖ := by
            rw [hdiff, norm_neg]
  have hnorm2 : ‖S_not‖ ≤ panTypeI_nonCoprimeDensity q m u := by
    calc
      ‖S_not‖
          ≤ ∑ n ∈ Finset.range (m + 1),
              ‖(if ¬ n.Coprime q then (vaughanFirst n u : ℂ) * ψ (n : ZMod χ.conductor) else 0)‖ := by
              simpa [S_not] using
                (norm_sum_le (s := Finset.range (m + 1))
                  (f := fun n =>
                    (if ¬ n.Coprime q then (vaughanFirst n u : ℂ) * ψ (n : ZMod χ.conductor)
                     else 0)))
      _ = ∑ n ∈ Finset.range (m + 1),
              (if ¬ n.Coprime q then ‖(vaughanFirst n u : ℂ) * ψ (n : ZMod χ.conductor)‖ else 0) := by
              apply Finset.sum_congr rfl
              intro n hn
              by_cases hc : n.Coprime q <;> simp [hc]
      _ ≤ ∑ n ∈ Finset.range (m + 1), (if ¬ n.Coprime q then |vaughanFirst n u| else 0) := by
              apply Finset.sum_le_sum
              intro n hn
              by_cases hc : n.Coprime q
              · simp [hc]
              · have hle : ‖(vaughanFirst n u : ℂ) * ψ (n : ZMod χ.conductor)‖ ≤ |vaughanFirst n u| := by
                  calc
                    ‖(vaughanFirst n u : ℂ) * ψ (n : ZMod χ.conductor)‖
                        ≤ ‖(vaughanFirst n u : ℂ)‖ * ‖ψ (n : ZMod χ.conductor)‖ := norm_mul_le _ _
                    _ = |vaughanFirst n u| * ‖ψ (n : ZMod χ.conductor)‖ := by
                          congr 1
                          exact RCLike.norm_ofReal (vaughanFirst n u)
                    _ ≤ |vaughanFirst n u| * 1 := by
                          exact mul_le_mul_of_nonneg_left
                            (dirichletChar_norm_le_one χ.conductor ψ (n : ZMod χ.conductor))
                            (abs_nonneg _)
                    _ = |vaughanFirst n u| := by simp
                simpa [hc] using hle
      _ = panTypeI_nonCoprimeDensity q m u := by
            unfold panTypeI_nonCoprimeDensity
            apply Finset.sum_congr rfl
            intro n hn
            by_cases hc : n.Coprime q <;> simp [hc, Nat.Coprime]
  simpa [ψ] using le_trans hnorm1 (add_le_add_right hnorm2 (‖panTypeIV1CharSum χ.conductor m u ψ‖))

/-! ### S2b: 分组双射与原特征平方和分解 (已证, 精确系数 1) -/

/-- 原特征部分: `P_{q'}(m) = Σ_{χ' 原特征 mod q'} ‖V_χ'(m)‖²`. -/
noncomputable def panTypeIPrimitiveSqSum (q' m u : ℕ) : ℝ :=
  ∑ χ' ∈ (Finset.univ : Finset (DirichletCharacter ℂ q')).filter (fun χ' => χ'.IsPrimitive),
    ‖panTypeIV1CharSum q' m u χ'‖ ^ 2

/-- changeLevel 的 dvd 证明项无关性. -/
lemma changeLevel_eq_of_dvd_proofs {R : Type*} [CommMonoidWithZero R] {n m : ℕ}
    (h₁ h₂ : n ∣ m) (χ : DirichletCharacter R n) :
    changeLevel h₁ χ = changeLevel h₂ χ := by
  have hh : h₁ = h₂ := Subsingleton.elim h₁ h₂
  rw [hh]

/-- **S2b (计数/分组双射, 已证)**: 反向映射 `(q', χ') ↦ changeLevel h χ'` 是
  `{(q', χ') : q' | q, χ' 原特征 mod q'}` 到 `{χ mod q}` 的双射
  (单射: conductor_changeLevel + changeLevel 单射; 满射: changeLevel_primitiveCharacter);
  故 `Σ_χ ‖V_{χ.primitiveCharacter}(m)‖² = Σ_{q' | q} P_{q'}(m)`.
  注意每个原特征 `χ' mod q'` 恰被**一个**模 q 特征诱导 (changeLevel 单射),
  因此系数是 1 而非 `φ(q)/φ(q')` (原 def 的核大小 `φ(q)/φ(q')` 是另一量, 与计数无关). -/
theorem panTypeI_primitiveRegroup (q m u : ℕ) [NeZero q] :
    (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ ^ 2) =
      ∑ q' ∈ q.divisors, panTypeIPrimitiveSqSum q' m u := by
  let s : Finset (Sigma fun q' : ℕ => DirichletCharacter ℂ q') :=
    (q.divisors).sigma (fun q' =>
      (Finset.univ : Finset (DirichletCharacter ℂ q')).filter (fun χ' => χ'.IsPrimitive))
  let i : ∀ p ∈ s, DirichletCharacter ℂ q := fun p hp =>
    changeLevel (Finset.mem_divisors.mp (Finset.mem_sigma.mp hp).1).1 p.2
  have hR : (∑ q' ∈ q.divisors, panTypeIPrimitiveSqSum q' m u) =
      (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ ^ 2) := by
    calc
      (∑ q' ∈ q.divisors, panTypeIPrimitiveSqSum q' m u)
          = ∑ p ∈ s, ‖panTypeIV1CharSum p.1 m u p.2‖ ^ 2 := by
            unfold panTypeIPrimitiveSqSum
            rw [Finset.sum_sigma]
      _ = (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ ^ 2) := by
            refine Finset.sum_bij (s := s) (t := Finset.univ)
              (f := fun p => ‖panTypeIV1CharSum p.1 m u p.2‖ ^ 2)
              (g := fun χ => ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ ^ 2)
              (i := i) ?_ ?_ ?_ ?_
            · intro p hp
              exact Finset.mem_univ _
            · -- inj
              intro p₁ hp₁ p₂ hp₂ h
              rcases p₁ with ⟨q'₁, χ'₁⟩
              rcases p₂ with ⟨q'₂, χ'₂⟩
              let h₁ : q'₁ ∣ q := (Finset.mem_divisors.mp (Finset.mem_sigma.mp hp₁).1).1
              let h₂ : q'₂ ∣ q := (Finset.mem_divisors.mp (Finset.mem_sigma.mp hp₂).1).1
              have hprim₁ : χ'₁.IsPrimitive := (Finset.mem_filter.mp (Finset.mem_sigma.mp hp₁).2).2
              have hprim₂ : χ'₂.IsPrimitive := (Finset.mem_filter.mp (Finset.mem_sigma.mp hp₂).2).2
              have hc₁ : (changeLevel h₁ χ'₁).conductor = q'₁ := by
                rw [DirichletCharacter.conductor_changeLevel (m := q) h₁, hprim₁]
              have hc₂ : (changeLevel h₂ χ'₂).conductor = q'₂ := by
                rw [DirichletCharacter.conductor_changeLevel (m := q) h₂, hprim₂]
              have hcc : (changeLevel h₁ χ'₁).conductor = (changeLevel h₂ χ'₂).conductor := by
                exact congrArg (fun η : DirichletCharacter ℂ q => η.conductor) h
              have hc : q'₁ = q'₂ := by
                rw [hc₁, hc₂] at hcc
                exact hcc
              subst hc
              have hh : h₁ = h₂ := Subsingleton.elim h₁ h₂
              have h' : changeLevel h₁ χ'₁ = changeLevel h₁ χ'₂ := by
                rw [← hh] at h
                exact h
              have hχ' : χ'₁ = χ'₂ := (changeLevel_injective (m := q) (R := ℂ) h₁) h'
              apply Sigma.ext rfl
              exact heq_of_eq hχ'
            · -- surj
              intro χ hχ
              let hp : ⟨χ.conductor, χ.primitiveCharacter⟩ ∈ s := by
                rw [Finset.mem_sigma]
                constructor
                · exact Finset.mem_divisors.mpr ⟨χ.conductor_dvd_level, (NeZero.ne q)⟩
                · rw [Finset.mem_filter]
                  constructor
                  · exact Finset.mem_univ _
                  · exact χ.primitiveCharacter_isPrimitive
              refine ⟨⟨χ.conductor, χ.primitiveCharacter⟩, hp, ?_⟩
              have hdvd : (Finset.mem_divisors.mp (Finset.mem_sigma.mp hp).1).1 =
                  χ.conductor_dvd_level := Subsingleton.elim _ _
              rw [hdvd]
              exact changeLevel_primitiveCharacter
            · -- h: f p = g (i p)
              intro p hp
              let h : p.1 ∣ q := (Finset.mem_divisors.mp (Finset.mem_sigma.mp hp).1).1
              have hprim : p.2.IsPrimitive := (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).2
              have hc : (changeLevel h p.2).conductor = p.1 := by
                rw [DirichletCharacter.conductor_changeLevel (m := q) h, hprim]
              have hsum : (∑ n ∈ Finset.range (m + 1),
                    (vaughanFirst n u : ℂ) * p.2 (n : ZMod p.1)) =
                  (∑ n ∈ Finset.range (m + 1),
                    (vaughanFirst n u : ℂ) *
                      (changeLevel h p.2).primitiveCharacter (n : ZMod p.1)) := by
                apply Finset.sum_congr rfl
                intro n hn
                congr 1
                have hpp : (changeLevel h p.2).primitiveCharacter (n : ZMod p.1) =
                    p.2.primitiveCharacter (n : ZMod p.1) := by
                  have hpp' := primitiveCharacter_changeLevel_apply (R := ℂ) h p.2 (n : ℤ)
                  rw [hc, hprim] at hpp'
                  simpa using hpp'
                have hself : p.2.primitiveCharacter (n : ZMod p.2.conductor) = p.2 (n : ZMod p.1) := by
                  by_cases hc' : n.Coprime p.2.conductor
                  · simpa using (p.2.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ))
                      (Nat.isCoprime_iff_coprime.mpr hc'))
                  · have hnu : ¬ IsUnit (n : ZMod p.2.conductor) :=
                      (ZMod.isUnit_iff_coprime n p.2.conductor).not.mpr hc'
                    have hcop' : ¬ n.Coprime p.1 := by
                      intro hcop
                      exact hc' (hcop.coprime_dvd_right p.2.conductor_dvd_level)
                    have hnu' : ¬ IsUnit (n : ZMod p.1) :=
                      (ZMod.isUnit_iff_coprime n p.1).not.mpr hcop'
                    rw [MulChar.map_nonunit p.2.primitiveCharacter hnu, MulChar.map_nonunit p.2 hnu']
                rw [hprim] at hself
                exact (hpp.trans hself).symm
              rw [hc]
              unfold panTypeIV1CharSum
              exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hsum
  exact hR.symm

/-- 代数块: `x ≤ y + d, 0 ≤ x, 0 ≤ d ⟹ x² ≤ 2y² + 2d²`. -/
lemma sq_le_two_sq_add_two_sq {x y d : ℝ} (h : x ≤ y + d) (hx : 0 ≤ x) (hd : 0 ≤ d) :
    x ^ 2 ≤ 2 * y ^ 2 + 2 * d ^ 2 := by
  have hy : 0 ≤ y + d := by linarith
  have h1 : x ^ 2 ≤ (y + d) ^ 2 := by
    rw [sq_le_sq]
    rw [abs_of_nonneg hx, abs_of_nonneg hy]
    exact h
  have h2 : (y + d) ^ 2 ≤ 2 * y ^ 2 + 2 * d ^ 2 := by
    nlinarith [sq_nonneg (y - d)]
  exact le_trans h1 h2

/-- **S2b (已证)**: 全特征平方和的原特征分解 (精确系数 1):
  `t_q(m) ≤ 2·Σ_{q' | q} P_{q'}(m) + 2·φ(q)·D_q(m)²`.
  (原 def 的 `φ(q)/φ(q')` 权重已修正: 诱导固定原特征 `χ'` 的模 q 特征恰有 1 个.) -/
theorem panTypeI_sqSum_primitiveDecomposition (q m u : ℕ) [NeZero q] :
    panTypeICharSqSum q m u ≤
      2 * (∑ q' ∈ q.divisors, panTypeIPrimitiveSqSum q' m u) +
        2 * (Nat.totient q : ℝ) * (panTypeI_nonCoprimeDensity q m u) ^ 2 := by
  unfold panTypeICharSqSum
  let D := panTypeI_nonCoprimeDensity q m u
  have hD : 0 ≤ D := by
    unfold D
    exact panTypeI_nonCoprimeDensity_nonneg q m u
  have hsq : ∀ χ : DirichletCharacter ℂ q,
      ‖panTypeIV1CharSum q m u χ‖ ^ 2 ≤
        2 * ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ ^ 2 + 2 * D ^ 2 := by
    intro χ
    exact sq_le_two_sq_add_two_sq (panTypeIV1CharSum_norm_le_primitive χ) (norm_nonneg _) hD
  calc
    (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q m u χ‖ ^ 2)
        ≤ ∑ χ : DirichletCharacter ℂ q,
            (2 * ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ ^ 2 + 2 * D ^ 2) := by
            exact Finset.sum_le_sum (fun χ hχ => hsq χ)
    _ = 2 * (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ ^ 2) +
          (∑ χ : DirichletCharacter ℂ q, 2 * D ^ 2) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = 2 * (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum χ.conductor m u χ.primitiveCharacter‖ ^ 2) +
          2 * (Nat.totient q : ℝ) * D ^ 2 := by
            haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ) := by
              exact AnalyticNumberTheory.LargeSieve.complexHasEnoughRootsOfUnity
                (Monoid.exponent (ZMod q)ˣ)
                (Monoid.exponent_ne_zero_of_finite (G := (ZMod q)ˣ))
            have hcard : Fintype.card (DirichletCharacter ℂ q) = Nat.totient q := by
              rw [← Nat.card_eq_fintype_card]
              exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
            rw [Finset.sum_const, Finset.card_univ, hcard]
            simp [nsmul_eq_mul]
            ring
    _ = 2 * (∑ q' ∈ q.divisors, panTypeIPrimitiveSqSum q' m u) +
          2 * (Nat.totient q : ℝ) * D ^ 2 := by
            rw [panTypeI_primitiveRegroup q m u]
    _ = 2 * (∑ q' ∈ q.divisors, panTypeIPrimitiveSqSum q' m u) +
          2 * (Nat.totient q : ℝ) * (panTypeI_nonCoprimeDensity q m u) ^ 2 := by
            unfold D

/-! ### S2c: 非互素密度 (结构已证; 密度估计开放) -/

/-- **S2c 结构 (已证)**: 非互素项被素数划分覆盖:
  `D_q(m) ≤ Σ_{p | q} Σ_{n ≤ m, p | n} |vf(n)|`
  (路线: `(n,q) > 1 ⟹ ∃ p | q, p | n`; 点式 `|vf| ≤ Σ_p 1_{p|n}|vf|`; 换序). -/
lemma panTypeI_nonCoprimeDensity_le_primePartition (q m u : ℕ) (hq : 0 < q) :
    panTypeI_nonCoprimeDensity q m u ≤
      ∑ p ∈ q.primeFactors,
        ∑ n ∈ Finset.range (m + 1), if p ∣ n then |vaughanFirst n u| else 0 := by
  unfold panTypeI_nonCoprimeDensity
  have hpoint : ∀ n : ℕ, ¬ n.Coprime q →
      (if ¬ n.Coprime q then |vaughanFirst n u| else 0) ≤
        ∑ p ∈ q.primeFactors, (if p ∣ n then |vaughanFirst n u| else 0) := by
    intro n hc
    simp [hc]
    have hg : n.gcd q ≠ 1 := by simpa [Nat.Coprime] using hc
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg
    have hpn : p ∣ n := dvd_trans hpd (Nat.gcd_dvd_left n q)
    have hpq : p ∣ q := dvd_trans hpd (Nat.gcd_dvd_right n q)
    have hp' : p ∈ q.primeFactors := (Nat.mem_primeFactors.mpr ⟨hp, hpq, Nat.ne_of_gt hq⟩)
    calc
      |vaughanFirst n u| = ∑ p ∈ ({p} : Finset ℕ), (if p ∣ n then |vaughanFirst n u| else 0) := by
            simp [hpn]
      _ ≤ ∑ p ∈ q.primeFactors, (if p ∣ n then |vaughanFirst n u| else 0) := by
            simpa using Finset.single_le_sum (fun p hp => by
              by_cases hpd : p ∣ n <;> simp [hpd, abs_nonneg]) hp'
  calc
    (∑ n ∈ Finset.range (m + 1), if ¬ n.Coprime q then |vaughanFirst n u| else 0)
        ≤ ∑ n ∈ Finset.range (m + 1),
            ∑ p ∈ q.primeFactors, (if p ∣ n then |vaughanFirst n u| else 0) := by
            exact Finset.sum_le_sum (fun n hn => by
              by_cases hc : n.Coprime q
              · simp [hc]
                exact Finset.sum_nonneg (fun p hp => by
                  by_cases hpd : p ∣ n <;> simp [hpd, abs_nonneg])
              · exact hpoint n hc)
    _ = ∑ p ∈ q.primeFactors,
          ∑ n ∈ Finset.range (m + 1), (if p ∣ n then |vaughanFirst n u| else 0) := by
          rw [Finset.sum_comm]
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
