/-
! # AnalyticNumberTheory.Sieve.PanVaughanPointwise

## 逐 q Vaughan 点式拆分的落地: 有限代数 + 解析台阶封装 (ant #15, VS2)

本文件推进 `PanVaughanPointwiseSplit` (PanAssembly.lean:91) 的落地, 分三层:

1. **有限代数 (零 sorry)**: 把 Vaughan 三段恒等式应用到等差 von Mangoldt
   计数 `apVonMangoldt` (PanMeanValueBody §4):

   - `vaughanIdentity_threeTerm_general`: 恒等式
     `Λ n = vaughanFirst n u - vaughanMiddle n u v + vaughanThird n u v`
     对所有 n 成立, 只需把 `n ≤ v` 的例外项显式写出
     (`vaughanFirst - vaughanMiddle + vaughanThird = if v < n then Λ n else 0`);
   - `apMiddle` / `apSmall`: 中间项 (type I') 与小因子例外项 (`n ≤ v`) 的等差计数;
   - `apVonMangoldt_eq_pieces`:
     `apVonMangoldt = apV1 - apMiddle + apV3 + apSmall` (精确等式);
   - `apVonMangoldt_abs_le_pieces` (三角不等式版):
     `|apVonMangoldt| ≤ |apV1| + |apV3| + |apMiddle| + |apSmall|`;
   - `panWeightedVonMangoldt_abs_le` (加权版): 对互素缩放和
     `Σ_{a ∈ Icc 1 X, (a,q)=1} f(a)·apVonMangoldt(y/a, q, l·a⁻¹ mod q)` 的
     三角拆分 (a-吸收后的实际形状).

2. **解析台阶**: `PanChebyshevApprox` -
   逐 (y,l) 点式拆分, 即 "Λ-计数 → 素数计数" 的 Chebyshev ψ↔π 转换与
   middle/small 主项吸收进 li 的 PNT 级内容 (Liu 2022 §III Thm 2;
   Halberstam--Richert 1974 Ch.10; 经典 Chebyshev: `ψ(y) = Σ_{n≤y} Λ(n) ≈
   π(y)·log y`). Section 8 (issue #44) 已落地 Chebyshev ψ↔π 的等差精确
   形式 (`apLogVonMangoldt` 恒等式, Vaughan log 加权拆分, 三角归约) 并把
   剩余解析内容精确封装为唯一台阶 `PanChebyshevMainStep`:
   `PanChebyshevApprox.of_mainStep` (需 `f 0 = 0`; 红队定理
   `not_PanChebyshevApprox_of_f0` 说明原陈述无此假设时为假).

3. **max 组合 (零 sorry)**: `panMaxL_le_pieces_sum` / `panMaxY_le_pieces_sum`
   把逐 (y,l) 点式拆分提升为双 max 形式
   (`max_{y'≤y} max_l |·| ≤ 三片段 max 之和`), 从而
   `PanVaughanPointwiseSplit.of_chebyshevApprox`:
   `PanChebyshevApprox ⇒ PanVaughanPointwiseSplit`.

装配 (PanAssembly.lean) 消费 `PanVaughanPointwiseSplit` 作为 `hsplit`,
与 `PanLogEventuallyLarge` 一起经 `PanVaughanSplit.of_analyticInputs`
给出 `PanMeanValueUniform` 的完整证明.

**红队注记 (ant #15, T3i 后续 — 拆分形状)**: 本文件的有限代数
`panWeightedVonMangoldt_abs_le` (加权 Vaughan 拆分) 的第三块是**带符号差**
`|Σ f(a)·(apSmall − apMiddle)|` (由 `apVonMangoldt_eq_pieces` 精确得出);
但解析台阶 `PanChebyshevApprox`/`PanVaughanPointwiseSplit` 把第三块写成
**纯 li 绝对值** `|Σ f(a)·li/φ(q)|`, 声称 middle/small 经 Möbius 反演吸收进
li 主项. 该形状是**错误**的: 即使 middle 因 `Σ_{d>u} μ(d)/d` 的 Möbius 尾部
消去而相对小 (`O(1/log u)`), 纯 |li| 块 `Σ_q w_q·Σ_a f(a)·|li(y/a)|/φ(q)`
(绝对值, 无权重相消) ≍ `(x/log x)·(1+log X)·log³Q` — 对任意固定 A 都
≫ `x/log^A x`. 经典 Liu §III 的正确形状: 第三块是 li 与 middle/small 的
**带符号差** (Chebyshev ψ↔π 转换后 `|Σ f(a)·((apSmall − apMiddle)/log(y/a)
− li(y/a)/φ(q))|`, PNT 级主项), 其 `x/log^A` 界需要 (a,q)=1 + Chen 权重
(a-调和和收敛) 与筛主项相减 (BRG). 修正拆分 (第三块 → 带符号差) 与主项子链
(`PanMainTermSieveBound`/`PanMainSieveAbsorption`) 的联合重设计见
`PAN_PROOF_ATLAS.md` 深析; 当前链 (`|li|` 形状) 的多对数闭合是诚实最大.
-/

import AnalyticNumberTheory.Sieve.PanAssembly

namespace AnalyticNumberTheory.Sieve

open Finset Real

open scoped Classical
open scoped ArithmeticFunction
open scoped ArithmeticFunction.Moebius

set_option maxHeartbeats 6000000
-- li 主项片段不依赖剩余类参数 l', 抑制相应告警 (同 PanMainTerm.lean).
set_option linter.unusedVariables false

noncomputable section

/-! ## 1. Vaughan 三段恒等式的全 n 形式 -/

/-- **Vaughan 三段恒等式 (全 n 形式)**: 对任意 `n u v : ℕ`,

  `vaughanFirst n u - vaughanMiddle n u v + vaughanThird n u v =
     if v < n then Λ n else 0`.

`vaughanIdentity_threeTerm` 只对 `v < n` 成立; 这里把 `n ≤ v` 的例外情形
显式化 (此时 `vaughanFullSecondSum` 给出
`vaughanSecond = Λ n - vaughanMiddle`, 抵消后三段和为 0). 纯有限卷积代数,
零 sorry. -/
theorem vaughanIdentity_threeTerm_general (n u v : ℕ) :
    vaughanFirst n u - vaughanMiddle n u v + vaughanThird n u v =
      if v < n then Λ n else 0 := by
  have hsplit : (∑ d ∈ n.divisors, ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v),
        ((μ d : ℤ) : ℝ) * Λ e) =
      (∑ d ∈ n.divisors.filter (fun d => u < d),
          ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v), ((μ d : ℤ) : ℝ) * Λ e) +
        (∑ d ∈ n.divisors.filter (fun d => d ≤ u),
          ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v), ((μ d : ℤ) : ℝ) * Λ e) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := n.divisors) (p := fun d => u < d)]
    have hfil : n.divisors.filter (fun d => ¬ u < d) = n.divisors.filter (fun d => d ≤ u) := by
      ext d
      simp [not_lt]
    rw [hfil]
  have hsecond : vaughanSecond n u v =
      (if n ≤ v then Λ n else 0) - vaughanMiddle n u v := by
    unfold vaughanSecond vaughanMiddle
    have hfull : (∑ d ∈ n.divisors, ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v),
        ((μ d : ℤ) : ℝ) * Λ e) = if n ≤ v then Λ n else 0 :=
      vaughanFullSecondSum n v
    have hAB : (∑ d ∈ n.divisors.filter (fun d => u < d),
          ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v), ((μ d : ℤ) : ℝ) * Λ e) +
        (∑ d ∈ n.divisors.filter (fun d => d ≤ u),
          ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v), ((μ d : ℤ) : ℝ) * Λ e) =
        if n ≤ v then Λ n else 0 := by
      rw [← hsplit]
      exact hfull
    linarith
  have hmain : vaughanFirst n u - vaughanMiddle n u v + vaughanThird n u v =
      Λ n - (if n ≤ v then Λ n else 0) := by
    have h1 := vaughanIdentity n u v
    linarith
  rw [hmain]
  by_cases hv : v < n
  · have hnle : ¬ n ≤ v := Nat.not_le_of_gt hv
    simp [hv, hnle]
  · have hnle : n ≤ v := Nat.not_lt.mp hv
    simp [hv, hnle]

/-! ## 2. 等差中间项与小项 -/

/-- **type I' 中间项的等差计数**: `Σ_{n ≤ y, n ≡ l [MOD q]} vaughanMiddle n u v`.
Vaughan 三段恒等式中 `-vaughanMiddle` 部分 (经典证明中经 Möbius 反演吸收进
li 主项). -/
noncomputable def apMiddle (y q l u v : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), if n ≡ l [MOD q] then vaughanMiddle n u v else 0

/-- **小因子例外项的等差计数**: `Σ_{n ≤ y, n ≡ l [MOD q], n ≤ v} Λ n`
(三段恒等式在 `n ≤ v` 时的例外项, 即 `ψ(min(y,v))` 的等差切片; 经典证明中
与 middle 项一起被 PNT 级主项吸收). -/
noncomputable def apSmall (y q l v : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), if n ≡ l [MOD q] then (if n ≤ v then Λ n else 0) else 0

/-! ## 3. apVonMangoldt 的 Vaughan 拆分 (有限代数) -/

/-- **apVonMangoldt 的精确 Vaughan 拆分**: 对任意 `y q l u v`,

  `apVonMangoldt y q l =
     apV1 y q l u - apMiddle y q l u v + apV3 y q l u v + apSmall y q l v`.

逐 n 应用 `vaughanIdentity_threeTerm_general` 并按同余类 `[MOD q]` 求和;
纯有限代数, 零 sorry. 这是 "type I + type II + 主项" 拆分在等差
von Mangoldt 计数上的精确形式. -/
theorem apVonMangoldt_eq_pieces (y q l u v : ℕ) :
    apVonMangoldt y q l =
      apV1 y q l u - apMiddle y q l u v + apV3 y q l u v + apSmall y q l v := by
  have hterm : ∀ n : ℕ,
      (if n ≡ l [MOD q] then Λ n else 0) =
        (if n ≡ l [MOD q] then vaughanFirst n u else 0) -
          (if n ≡ l [MOD q] then vaughanMiddle n u v else 0) +
          (if n ≡ l [MOD q] then vaughanThird n u v else 0) +
          (if n ≡ l [MOD q] then (if n ≤ v then Λ n else 0) else 0) := by
    intro n
    by_cases hmod : n ≡ l [MOD q]
    · simp [hmod]
      rw [vaughanIdentity_threeTerm_general n u v]
      by_cases hv : v < n
      · have hnle : ¬ n ≤ v := Nat.not_le_of_gt hv
        simp [hv, hnle]
      · have hnle : n ≤ v := Nat.not_lt.mp hv
        simp [hv, hnle]
    · simp [hmod]
  calc
    apVonMangoldt y q l
        = ∑ n ∈ Finset.range (y + 1), (if n ≡ l [MOD q] then Λ n else 0) := rfl
    _ = ∑ n ∈ Finset.range (y + 1),
            ((if n ≡ l [MOD q] then vaughanFirst n u else 0) -
              (if n ≡ l [MOD q] then vaughanMiddle n u v else 0) +
              (if n ≡ l [MOD q] then vaughanThird n u v else 0) +
              (if n ≡ l [MOD q] then (if n ≤ v then Λ n else 0) else 0)) := by
          exact Finset.sum_congr rfl (fun n hn => hterm n)
    _ = (∑ n ∈ Finset.range (y + 1), (if n ≡ l [MOD q] then vaughanFirst n u else 0)) -
          (∑ n ∈ Finset.range (y + 1), (if n ≡ l [MOD q] then vaughanMiddle n u v else 0)) +
          (∑ n ∈ Finset.range (y + 1), (if n ≡ l [MOD q] then vaughanThird n u v else 0)) +
          (∑ n ∈ Finset.range (y + 1),
            (if n ≡ l [MOD q] then (if n ≤ v then Λ n else 0) else 0)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = apV1 y q l u - apMiddle y q l u v + apV3 y q l u v + apSmall y q l v := rfl

/-- **apVonMangoldt 的三角不等式拆分**: 对任意 `y q l u v`,

  `|apVonMangoldt y q l| ≤
     |apV1 y q l u| + |apV3 y q l u v| + |apMiddle y q l u v| + |apSmall y q l v|`.

由 `apVonMangoldt_eq_pieces` + 三角不等式 (逐项绝对值) 直接得到; 零 sorry. -/
theorem apVonMangoldt_abs_le_pieces (y q l u v : ℕ) :
    |apVonMangoldt y q l| ≤
      |apV1 y q l u| + |apV3 y q l u v| + |apMiddle y q l u v| + |apSmall y q l v| := by
  rw [apVonMangoldt_eq_pieces]
  have h1 : |apV1 y q l u - apMiddle y q l u v| ≤ |apV1 y q l u| + |apMiddle y q l u v| := by
    have h := abs_add_le (apV1 y q l u) (-apMiddle y q l u v)
    simpa [sub_eq_add_neg, abs_neg] using h
  have h2 : |(apV1 y q l u - apMiddle y q l u v) + apV3 y q l u v| ≤
      |apV1 y q l u - apMiddle y q l u v| + |apV3 y q l u v| := by
    exact abs_add_le (apV1 y q l u - apMiddle y q l u v) (apV3 y q l u v)
  have h3 : |((apV1 y q l u - apMiddle y q l u v) + apV3 y q l u v) + apSmall y q l v| ≤
      |(apV1 y q l u - apMiddle y q l u v) + apV3 y q l u v| + |apSmall y q l v| := by
    exact abs_add_le ((apV1 y q l u - apMiddle y q l u v) + apV3 y q l u v) (apSmall y q l v)
  linarith

/-! ## 4. 加权版的三角拆分 (a-吸收后的形状) -/

/-- 有限集上三重和的三角界: `|Σ (A + (B + C))| ≤ |Σ A| + (|Σ B| + |Σ C|)`. -/
private lemma abs_sum_add_add_le (s : Finset ℕ) (A B C : ℕ → ℝ) :
    |∑ a ∈ s, (A a + (B a + C a))| ≤ |∑ a ∈ s, A a| + (|∑ a ∈ s, B a| + |∑ a ∈ s, C a|) := by
  calc
    |∑ a ∈ s, (A a + (B a + C a))| ≤ |∑ a ∈ s, A a| + |∑ a ∈ s, (B a + C a)| := by
      rw [Finset.sum_add_distrib]
      exact abs_add_le (∑ a ∈ s, A a) (∑ a ∈ s, (B a + C a))
    _ ≤ |∑ a ∈ s, A a| + (|∑ a ∈ s, B a| + |∑ a ∈ s, C a|) := by
      have hBC : |∑ a ∈ s, (B a + C a)| ≤ |∑ a ∈ s, B a| + |∑ a ∈ s, C a| := by
        rw [Finset.sum_add_distrib]
        exact abs_add_le (∑ a ∈ s, B a) (∑ a ∈ s, C a)
      linarith

/-- **加权 Vaughan 拆分 (a-吸收后的形状)**: 对互素缩放和,

  `|Σ_{a ∈ Icc 1 X, (a,q)=1} f(a)·apVonMangoldt(y/a, q, l·a⁻¹ mod q)| ≤
     |Σ f(a)·apV1(...)| + |Σ f(a)·apV3(...)| +
     |Σ f(a)·(apSmall(...) - apMiddle(...))|`.

由 `apVonMangoldt_eq_pieces` 逐 a 代入 + 线性 + 三角不等式; 零 sorry.
这是装配中层 "Λ-计数 → 素数计数" (Chebyshev ψ↔π) 之前, 加权和上的
type I / type II / 主项 三角拆分. -/
theorem panWeightedVonMangoldt_abs_le (y X q l u v : ℕ) (f : ℕ → ℝ) :
    |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * apVonMangoldt (y / a) q (natInvMod q a * l % q) else 0| ≤
      |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * apV1 (y / a) q (natInvMod q a * l % q) u else 0| +
      |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * apV3 (y / a) q (natInvMod q a * l % q) u v else 0| +
      |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * (apSmall (y / a) q (natInvMod q a * l % q) v -
          apMiddle (y / a) q (natInvMod q a * l % q) u v) else 0| := by
  have hterm : ∀ a ∈ Finset.Icc 1 X,
      (if a.Coprime q then f a * apVonMangoldt (y / a) q (natInvMod q a * l % q) else 0) =
        (if a.Coprime q then f a * apV1 (y / a) q (natInvMod q a * l % q) u else 0) +
          ((if a.Coprime q then f a * apV3 (y / a) q (natInvMod q a * l % q) u v else 0) +
            (if a.Coprime q then
                f a * (apSmall (y / a) q (natInvMod q a * l % q) v -
                  apMiddle (y / a) q (natInvMod q a * l % q) u v)
              else 0)) := by
    intro a ha
    by_cases hcop : a.Coprime q
    · simp only [if_pos hcop]
      rw [apVonMangoldt_eq_pieces]
      ring_nf
    · simp [hcop]
  calc
    |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * apVonMangoldt (y / a) q (natInvMod q a * l % q) else 0|
        = |∑ a ∈ Finset.Icc 1 X,
            ((if a.Coprime q then f a * apV1 (y / a) q (natInvMod q a * l % q) u else 0) +
              ((if a.Coprime q then f a * apV3 (y / a) q (natInvMod q a * l % q) u v else 0) +
                (if a.Coprime q then
                    f a * (apSmall (y / a) q (natInvMod q a * l % q) v -
                      apMiddle (y / a) q (natInvMod q a * l % q) u v)
                  else 0)))| := by
          congr 1
          exact Finset.sum_congr rfl (fun a ha => hterm a ha)
    _ ≤ |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
            f a * apV1 (y / a) q (natInvMod q a * l % q) u else 0| +
          (|∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * apV3 (y / a) q (natInvMod q a * l % q) u v else 0| +
            |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
                f a * (apSmall (y / a) q (natInvMod q a * l % q) v -
                  apMiddle (y / a) q (natInvMod q a * l % q) u v)
              else 0|) := by
          exact abs_sum_add_add_le (Finset.Icc 1 X)
            (fun a => if a.Coprime q then f a * apV1 (y / a) q (natInvMod q a * l % q) u else 0)
            (fun a => if a.Coprime q then f a * apV3 (y / a) q (natInvMod q a * l % q) u v else 0)
            (fun a => if a.Coprime q then
                f a * (apSmall (y / a) q (natInvMod q a * l % q) v -
                  apMiddle (y / a) q (natInvMod q a * l % q) u v)
              else 0)
    _ ≤ |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
            f a * apV1 (y / a) q (natInvMod q a * l % q) u else 0| +
          |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
            f a * apV3 (y / a) q (natInvMod q a * l % q) u v else 0| +
          |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
            f a * (apSmall (y / a) q (natInvMod q a * l % q) v -
              apMiddle (y / a) q (natInvMod q a * l % q) u v)
            else 0| := by
          linarith

/-! ## 5. 解析台阶: `PanChebyshevApprox` (逐 (y,l) 点式拆分) -/

/-- **解析台阶 (Chebyshev ψ↔π + 主项吸收, 逐 (y,l) 点式)**: 对每个模 `q`,
剩余类 `l` ((l,q)=1) 与截断 `y`,

  `|panDistributionSum y X q l f| ≤
     |panPieceSum y X q l f (fun y q l => apV1 y q l u / log y)| +
     |panPieceSum y X q l f (fun y q l => apV3 y q l u v / log y)| +
     |panPieceSum y X q l f (fun y q l => li y / φ(q))|`.

经典内容 (Liu 2022 §III Thm 2; Halberstam--Richert 1974 Ch.10):
  `π(y; q, l)·log y ≈ Σ_{n ≤ y, n ≡ l [MOD q]} Λ(n)`  (Chebyshev ψ↔π 的等差形式)
经 Vaughan 三段恒等式 (VaughanIdentity.lean) 把 `apVonMangoldt` 拆成
type I (apV1) + type II (apV3) + middle/small, 后者与 `li` 主项经 PNT 级
吸收合并; `a = 0` 项 (仅 `q = 1` 非零) 与 `li` 实/整参数取整差异同属此台阶.
这是 `PanVaughanPointwiseSplit` 归约后剩下的唯一解析输入 (不引入公理,
不 sorry; 以 Prop 封装, 供后续落地).

> ⚠️ **红队 (issue #44 复查)**: 本陈述的第三块是**纯 `|li/φ(q)|`**, 装配后是
> 多对数不可吸收: `Σ_{q≤Q} μ²(q)3^ω(q)/φ(q) ≈ (log Q)^{O(1)}` 增长, 而
> `panPieceMaxY(li/φ(q)) ≥ (1/φ(q))·Σ_{a≤X}|f(a)|·li(⌊y/a⌋) ≈ y·log X/(φ(q)log y)`,
> 乘积 ≈ `y·polylog` 不可被 `C·y/log^A y` 压制 (f ≡ 1 即反例; 也见
> `PanMainTerm.lean` 模块头红队注记). 正确形态是 **li 吸收 middle/small**
> (三块之一, 见 Section 9 的 `PanChebyshevApproxCorrected` 与精确结构定理
> `panDistributionSum_abs_le_logPieces_mainBlock`); 本陈述保留仅供
> `PanVaughanPointwiseSplit.of_chebyshevApprox` 的装配链与红队对比. -/
def PanChebyshevApprox (f : ℕ → ℝ) (u v : ℕ) : Prop :=
  ∀ X q y l : ℕ, 0 < q → l.Coprime q →
    |panDistributionSum y X q l f| ≤
      |panPieceSum y X q l f (fun y q l => apV1 y q l u / Real.log (y : ℝ))| +
      |panPieceSum y X q l f (fun y q l => apV3 y q l u v / Real.log (y : ℝ))| +
      |panPieceSum y X q l f (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q)|

/-! ## 6. max 组合: 逐 (y,l) 点式拆分 → 双 max 形式 (有限代数) -/

/-- 片段 l-max 非负 (q ≤ 1 时 l-集为空取 0). 镜像 PanAssembly 的私有版本. -/
private lemma panPieceMaxL_nonneg (y X q : ℕ) (f : ℕ → ℝ) (g : ℕ → ℕ → ℕ → ℝ) :
    0 ≤ panPieceMaxL y X q f g := by
  unfold panPieceMaxL
  by_cases h : ((Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q)).Nonempty
  · dsimp only []
    rw [dif_pos h]
    rcases h with ⟨l, hl⟩
    have hl' : |panPieceSum y X q l f g| ∈
        (Finset.image (fun l : ℕ => |panPieceSum y X q l f g|)
          ((Finset.Icc 1 (q - 1)).filter (fun l : ℕ => l.Coprime q))) := by
      exact Finset.mem_image.mpr ⟨l, hl, rfl⟩
    exact le_trans (abs_nonneg _) (Finset.le_max' _ _ hl')
  · dsimp only []
    rw [dif_neg h]

/-- **l-max 归约**: 逐 (y,l) 点式拆分 ⇒ `panMaxL ≤ 三片段 panPieceMaxL 之和`
(逐 l 的绝对值三角不等式后取 max; l-集为空时平凡). -/
theorem panMaxL_le_pieces_sum (y X q : ℕ) (f : ℕ → ℝ) (g1 g2 g3 : ℕ → ℕ → ℕ → ℝ)
    (h : ∀ l : ℕ, l.Coprime q →
      |panDistributionSum y X q l f| ≤
        |panPieceSum y X q l f g1| + |panPieceSum y X q l f g2| + |panPieceSum y X q l f g3|) :
    panMaxL y X q f ≤
      panPieceMaxL y X q f g1 + panPieceMaxL y X q f g2 + panPieceMaxL y X q f g3 := by
  unfold panMaxL panPieceMaxL
  dsimp only []
  by_cases hS : ((Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q)).Nonempty
  · simp only [dif_pos hS]
    apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨l, hl, rfl⟩
    have hlcop : l.Coprime q := (Finset.mem_filter.mp hl).2
    have hineq := h l hlcop
    have h1 : |panPieceSum y X q l f g1| ≤
        (((Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q)).image
          (fun l : ℕ => |panPieceSum y X q l f g1|)).max'
          (Finset.image_nonempty.mpr hS) := by
      exact Finset.le_max'
        (s := ((Finset.Icc 1 (q - 1)).filter (fun l : ℕ => l.Coprime q)).image
          (fun l : ℕ => |panPieceSum y X q l f g1|))
        (x := |panPieceSum y X q l f g1|)
        (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    have h2 : |panPieceSum y X q l f g2| ≤
        (((Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q)).image
          (fun l : ℕ => |panPieceSum y X q l f g2|)).max'
          (Finset.image_nonempty.mpr hS) := by
      exact Finset.le_max'
        (s := ((Finset.Icc 1 (q - 1)).filter (fun l : ℕ => l.Coprime q)).image
          (fun l : ℕ => |panPieceSum y X q l f g2|))
        (x := |panPieceSum y X q l f g2|)
        (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    have h3 : |panPieceSum y X q l f g3| ≤
        (((Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q)).image
          (fun l : ℕ => |panPieceSum y X q l f g3|)).max'
          (Finset.image_nonempty.mpr hS) := by
      exact Finset.le_max'
        (s := ((Finset.Icc 1 (q - 1)).filter (fun l : ℕ => l.Coprime q)).image
          (fun l : ℕ => |panPieceSum y X q l f g3|))
        (x := |panPieceSum y X q l f g3|)
        (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    nlinarith [hineq, h1, h2, h3]
  · simp [dif_neg hS]

/-- **y-max 归约**: 逐 (y,l) 点式拆分 ⇒ `panMaxY ≤ 三片段 panPieceMaxY 之和`
(对每个 `y' ≤ x` 用 l-max 归约后取 y-max; `max_{y'} Σᵢ ≤ Σᵢ max_{y'}`). -/
theorem panMaxY_le_pieces_sum (X q x : ℕ) (f : ℕ → ℝ) (g1 g2 g3 : ℕ → ℕ → ℕ → ℝ)
    (h : ∀ y' : ℕ, ∀ l : ℕ, l.Coprime q →
      |panDistributionSum y' X q l f| ≤
        |panPieceSum y' X q l f g1| + |panPieceSum y' X q l f g2| + |panPieceSum y' X q l f g3|) :
    panMaxY X q x f ≤
      panPieceMaxY X q x f g1 + panPieceMaxY X q x f g2 + panPieceMaxY X q x f g3 := by
  have hy : ∀ y' ∈ Finset.range (x + 1),
      panMaxL y' X q f ≤
        panPieceMaxL y' X q f g1 + panPieceMaxL y' X q f g2 + panPieceMaxL y' X q f g3 := by
    intro y' hy'
    exact panMaxL_le_pieces_sum y' X q f g1 g2 g3 (h y')
  unfold panMaxY panPieceMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y', hy', rfl⟩
  have h1 : panPieceMaxL y' X q f g1 ≤
      ((Finset.range (x + 1)).image (fun y => panPieceMaxL y X q f g1)).max'
        (Finset.image_nonempty.mpr ⟨0, by simp⟩) := by
    exact Finset.le_max'
      (s := (Finset.range (x + 1)).image (fun y => panPieceMaxL y X q f g1))
      (x := panPieceMaxL y' X q f g1)
      (Finset.mem_image.mpr ⟨y', hy', rfl⟩)
  have h2 : panPieceMaxL y' X q f g2 ≤
      ((Finset.range (x + 1)).image (fun y => panPieceMaxL y X q f g2)).max'
        (Finset.image_nonempty.mpr ⟨0, by simp⟩) := by
    exact Finset.le_max'
      (s := (Finset.range (x + 1)).image (fun y => panPieceMaxL y X q f g2))
      (x := panPieceMaxL y' X q f g2)
      (Finset.mem_image.mpr ⟨y', hy', rfl⟩)
  have h3 : panPieceMaxL y' X q f g3 ≤
      ((Finset.range (x + 1)).image (fun y => panPieceMaxL y X q f g3)).max'
        (Finset.image_nonempty.mpr ⟨0, by simp⟩) := by
    exact Finset.le_max'
      (s := (Finset.range (x + 1)).image (fun y => panPieceMaxL y X q f g3))
      (x := panPieceMaxL y' X q f g3)
      (Finset.mem_image.mpr ⟨y', hy', rfl⟩)
  nlinarith [hy y' hy', h1, h2, h3]

/-! ## 7. 目标: `PanVaughanPointwiseSplit.of_chebyshevApprox` -/

/-- **目标定理**: 解析台阶 `PanChebyshevApprox` (逐 (y,l) 点式拆分) ⇒
`PanVaughanPointwiseSplit` (双 max 形式). 全部有限代数 (三角拆分, l-max/y-max
组合) 在此证明; 零 sorry, 唯一剩余解析输入是 `PanChebyshevApprox` 本身. -/
theorem PanVaughanPointwiseSplit.of_chebyshevApprox {x : ℕ → ℝ} {f : ℕ → ℝ} {u v : ℕ}
    (h : PanChebyshevApprox f u v) : PanVaughanPointwiseSplit x f u v := by
  intro X q y hq
  exact panMaxY_le_pieces_sum X q y f
    (fun y q l => apV1 y q l u / Real.log (y : ℝ))
    (fun y q l => apV3 y q l u v / Real.log (y : ℝ))
    (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q)
    (fun y' l hl => h X q y' l hq hl)

/-! ## 8. Chebyshev ψ↔π 等差精确形式与 `PanChebyshevApprox` 归约 (issue #44)

本节把 Section 5 的开放 Prop `PanChebyshevApprox` 归约到唯一解析台阶
`PanChebyshevMainStep`, 并落地 Chebyshev ψ↔π 的等差精确形式:

1. **精确恒等式**: `Σ_{n ≤ y, n ≡ l [MOD q]} Λ(n)/log n = π(y; q, l) + PP`
   (素数次幂修正): 素数贡献 1 (`Λ p/log p = 1`), 素数次幂 `p^k` (k ≥ 2)
   贡献 1/k, 其余为 0. `apLogVonMangoldt_eq_primesInAP_add_pp`.
2. **a-吸收**: 对 (a,q) = 1, `Σ_{n ≤ y/a, n ≡ a⁻¹l} Λ(n)/log n =
   π(y; a, q, l) + PP` (`apLogVonMangoldt_eq_primesInAPBelow_inv`).
3. **Vaughan 拆分**: log 加权 von Mangoldt 和的四段精确拆分
   (`apLogVonMangoldt_eq_logPieces`).
4. **三角归约**: `|panDistributionSum| ≤ |素数计数和| + |li 主项和|`
   (`panDistributionSum_abs_le_primes_li`); 代入精确恒等式得主项形式
   `panDistributionSum_eq_mainStep`.
5. **唯一剩余解析台阶** `PanChebyshevMainStep`: log 加权 Λ 和 (ψ/log 侧)
   被 type I (apV1/log) + type III (apV3/log) + 对数积分主项 `li/φ(q)`
   控制, 中间项/小项/素数次幂修正/取整差异全部被主项吸收 (Liu 2022 §III
   Thm 2; Halberstam--Richert 1974 Ch.10; 经典 Möbius 反演 + PNT 级估计).
   由 `PanChebyshevApprox.of_mainStep` 归约出 `PanChebyshevApprox`.
6. **红队**: 原陈述 (无 `f 0 = 0`) 为假 (`not_PanChebyshevApprox_of_f0`):
   `a = 0` 项仅 q = 1 时非零, 经典陈述的 a 从 1 开始; 修复为 `f 0 = 0`. -/

/-- 加权 von Mangoldt 的 log 归一和: `Σ_{n ≤ y, n ≡ l [MOD q]} Λ(n)/log n`.
每个素数 n = p 贡献 1 (`Λ p / log p = 1`), 每个素数次幂 n = p^k (k ≥ 2)
贡献 1/k; 这是 Chebyshev ψ↔π 转换中的 `ψ/log` 侧. -/
noncomputable def apLogVonMangoldt (y q l : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), if n ≡ l [MOD q] then Λ n / Real.log (n : ℝ) else 0

/-- 素数次幂修正 (k ≥ 2 部分): `Σ_{p^k ≤ y, k ≥ 2, p^k ≡ l [MOD q]} 1/k`.
由 `Λ p^k / log p^k = 1/k` 与 `Λ n = 0` (非素数次幂) 得到. -/
noncomputable def apPrimePowerCorrection (y q l : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), if n ≡ l [MOD q] then (if n.Prime then 0 else Λ n / Real.log (n : ℝ)) else 0

/-- 素数 n 的 von Mangoldt 值: `Λ p = log p` (由 `μ ∗ log = Λ` 在
`p.divisors = {1, p}` 上求值). -/
lemma vonMangoldt_eq_log_of_prime {p : ℕ} (hp : p.Prime) : Λ p = Real.log (p : ℝ) := by
  have hΛ1 : Λ (1 : ℕ) = 0 := by
    rw [ArithmeticFunction.vonMangoldt_apply]
    have hpp : ¬ IsPrimePow (1 : ℕ) := by
      intro h1
      exact IsPrimePow.ne_one h1 rfl
    simp [hpp]
  have hsum := ArithmeticFunction.vonMangoldt_sum (n := p)
  rw [Nat.Prime.divisors hp] at hsum
  have hne : (1 : ℕ) ≠ p := hp.ne_one.symm
  rw [Finset.sum_pair hne] at hsum
  rw [hΛ1] at hsum
  simpa [add_comm] using hsum

/-- von Mangoldt 非负. -/
lemma vonMangoldt_nonneg (n : ℕ) : 0 ≤ Λ n := by
  rw [ArithmeticFunction.vonMangoldt_apply]
  by_cases h : IsPrimePow n
  · rw [if_pos h]
    have hmin : 0 < n.minFac := Nat.minFac_pos n
    have hle : 1 ≤ (n.minFac : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hmin)
    exact Real.log_nonneg hle
  · rw [if_neg h]

/-- 自然数实值对数非负: `0 ≤ log n` 对所有 n (含 n = 0). -/
private lemma nat_log_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · exact Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)))

/-- 素数次幂修正非负. -/
theorem apPrimePowerCorrection_nonneg (y q l : ℕ) : 0 ≤ apPrimePowerCorrection y q l := by
  unfold apPrimePowerCorrection
  refine Finset.sum_nonneg ?_
  intro n hn
  by_cases hmod : n ≡ l [MOD q]
  · simp [hmod]
    by_cases hp : n.Prime
    · simp [hp]
    · simp [hp]
      exact div_nonneg (vonMangoldt_nonneg n) (nat_log_nonneg n)
  · simp [hmod]

/-- **Chebyshev ψ↔π 等差精确恒等式**:
`Σ_{n ≤ y, n ≡ l [MOD q]} Λ(n)/log n = π(y; q, l) + (素数次幂修正)`.
逐 n 项: 素数贡献 1 (被 `primesInAP` 计数), 非素数素数次幂贡献 1/k
(被 `apPrimePowerCorrection` 计数), 其余贡献 0. -/
theorem apLogVonMangoldt_eq_primesInAP_add_pp (y q l : ℕ) :
    apLogVonMangoldt y q l = (primesInAP y q l : ℝ) + apPrimePowerCorrection y q l := by
  have hprimes : (primesInAP y q l : ℝ) =
      ∑ n ∈ Finset.range (y + 1), if (n.Prime ∧ n ≡ l [MOD q]) then (1 : ℝ) else 0 := by
    unfold primesInAP
    calc
      ((((Finset.range (y + 1)).filter (fun p => p.Prime ∧ p ≡ l [MOD q])).card : ℕ) : ℝ)
          = ∑ x ∈ (Finset.range (y + 1)).filter (fun p => p.Prime ∧ p ≡ l [MOD q]), (1 : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ∑ n ∈ Finset.range (y + 1), if (n.Prime ∧ n ≡ l [MOD q]) then (1 : ℝ) else 0 := by
            rw [Finset.sum_filter]
  rw [hprimes]
  unfold apPrimePowerCorrection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hmod : n ≡ l [MOD q]
  · simp [hmod]
    by_cases hp : n.Prime
    · have hΛ : Λ n = Real.log (n : ℝ) := vonMangoldt_eq_log_of_prime hp
      have hlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (Nat.Prime.one_lt hp))).ne'
      rw [hΛ]
      rw [div_self hlog]
      simp [hp]
    · simp [hp]
  · simp [hmod]

/-- **a-吸收的 Chebyshev 恒等式**: 对 (a,q) = 1, a ≥ 1,
`Σ_{n ≤ y/a, n ≡ a⁻¹l} Λ(n)/log n = π(y; a, q, l) + (素数次幂修正)`. -/
theorem apLogVonMangoldt_eq_primesInAPBelow_inv (y a q l : ℕ) (ha : 0 < a) (hcop : a.Coprime q) :
    apLogVonMangoldt (y / a) q (natInvMod q a * l % q) =
      (primesInAPBelow y a q l : ℝ) +
        apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) := by
  rw [apLogVonMangoldt_eq_primesInAP_add_pp (y / a) q (natInvMod q a * l % q)]
  congr 1
  rw [primesInAPBelow_eq_primesInAP_inv y a q l ha hcop]

/-- type I 片段的 log 加权形式. -/
noncomputable def apV1Log (y q l u : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), if n ≡ l [MOD q] then vaughanFirst n u / Real.log (n : ℝ) else 0

/-- type II (V3) 片段的 log 加权形式. -/
noncomputable def apV3Log (y q l u v : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), if n ≡ l [MOD q] then vaughanThird n u v / Real.log (n : ℝ) else 0

/-- 中间项 (type I') 的 log 加权形式. -/
noncomputable def apMiddleLog (y q l u v : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), if n ≡ l [MOD q] then vaughanMiddle n u v / Real.log (n : ℝ) else 0

/-- 小因子例外项的 log 加权形式. -/
noncomputable def apSmallLog (y q l v : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1),
    if n ≡ l [MOD q] then (if n ≤ v then Λ n else 0) / Real.log (n : ℝ) else 0

/-- **log 加权 von Mangoldt 和的 Vaughan 拆分**:
`Σ Λ(n)/log n = Σ V1/log n - Σ middle/log n + Σ V3/log n + Σ small/log n`.
逐 n 应用 `vaughanIdentity_threeTerm_general` 后除以 `log n` (域恒等式,
log n = 0 时两边都平凡). -/
theorem apLogVonMangoldt_eq_logPieces (y q l u v : ℕ) :
    apLogVonMangoldt y q l =
      apV1Log y q l u - apMiddleLog y q l u v + apV3Log y q l u v + apSmallLog y q l v := by
  have hterm : ∀ n : ℕ, (if n ≡ l [MOD q] then Λ n / Real.log (n : ℝ) else 0) =
      (if n ≡ l [MOD q] then vaughanFirst n u / Real.log (n : ℝ) else 0) -
        (if n ≡ l [MOD q] then vaughanMiddle n u v / Real.log (n : ℝ) else 0) +
        (if n ≡ l [MOD q] then vaughanThird n u v / Real.log (n : ℝ) else 0) +
        (if n ≡ l [MOD q] then (if n ≤ v then Λ n else 0) / Real.log (n : ℝ) else 0) := by
    intro n
    by_cases hmod : n ≡ l [MOD q]
    · simp [hmod]
      have hsub : Λ n = vaughanFirst n u - vaughanMiddle n u v + vaughanThird n u v +
          (if n ≤ v then Λ n else 0) := by
        have h1 := vaughanIdentity_threeTerm_general n u v
        by_cases hv : v < n
        · rw [if_pos hv] at h1
          have hsmall : (if n ≤ v then Λ n else 0) = 0 := by
            have : ¬ n ≤ v := Nat.not_le_of_gt hv
            simp [this]
          rw [hsmall]
          linarith
        · rw [if_neg hv] at h1
          have hsmall : (if n ≤ v then Λ n else 0) = Λ n := by
            have : n ≤ v := Nat.not_lt.mp hv
            simp [this]
          rw [hsmall]
          linarith
      calc
        Λ n / Real.log (n : ℝ) =
            (vaughanFirst n u - vaughanMiddle n u v + vaughanThird n u v +
              (if n ≤ v then Λ n else 0)) / Real.log (n : ℝ) := by
          conv_lhs => rw [hsub]
        _ = vaughanFirst n u / Real.log (n : ℝ) - vaughanMiddle n u v / Real.log (n : ℝ) +
              vaughanThird n u v / Real.log (n : ℝ) +
              (if n ≤ v then Λ n else 0) / Real.log (n : ℝ) := by
          ring
    · simp [hmod]
  calc
    apLogVonMangoldt y q l
        = ∑ n ∈ Finset.range (y + 1), (if n ≡ l [MOD q] then Λ n / Real.log (n : ℝ) else 0) := rfl
    _ = ∑ n ∈ Finset.range (y + 1),
            ((if n ≡ l [MOD q] then vaughanFirst n u / Real.log (n : ℝ) else 0) -
              (if n ≡ l [MOD q] then vaughanMiddle n u v / Real.log (n : ℝ) else 0) +
              (if n ≡ l [MOD q] then vaughanThird n u v / Real.log (n : ℝ) else 0) +
              (if n ≡ l [MOD q] then (if n ≤ v then Λ n else 0) / Real.log (n : ℝ) else 0)) := by
          exact Finset.sum_congr rfl (fun n hn => hterm n)
    _ = apV1Log y q l u - apMiddleLog y q l u v + apV3Log y q l u v + apSmallLog y q l v := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
          rfl

/-- **三角归约**: `|panDistributionSum| ≤ |素数计数和| + |li 主项和|`
(展开 `panDistributionError = π - li/φ` 后逐项三角不等式). -/
theorem panDistributionSum_abs_le_primes_li (y X q l : ℕ) (f : ℕ → ℝ) :
    |panDistributionSum y X q l f| ≤
      |∑ a ∈ Finset.range (X + 1), if a.Coprime q then
          f a * (primesInAPBelow y a q l : ℝ) else 0| +
        |∑ a ∈ Finset.range (X + 1), if a.Coprime q then
          f a * (logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| := by
  unfold panDistributionSum panDistributionError
  have hsplit : (∑ a ∈ Finset.range (X + 1), if a.Coprime q then
        f a * ((primesInAPBelow y a q l : ℝ) - logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0) =
      (∑ a ∈ Finset.range (X + 1), if a.Coprime q then
          f a * (primesInAPBelow y a q l : ℝ) else 0) -
        (∑ a ∈ Finset.range (X + 1), if a.Coprime q then
          f a * (logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hcop : a.Coprime q
    · rw [if_pos hcop, if_pos hcop, if_pos hcop]
      ring
    · rw [if_neg hcop, if_neg hcop, if_neg hcop]
      ring
  rw [hsplit]
  have h1 : |(∑ a ∈ Finset.range (X + 1), if a.Coprime q then
        f a * (primesInAPBelow y a q l : ℝ) else 0) -
      (∑ a ∈ Finset.range (X + 1), if a.Coprime q then
        f a * (logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0)| ≤
      |∑ a ∈ Finset.range (X + 1), if a.Coprime q then
        f a * (primesInAPBelow y a q l : ℝ) else 0| +
        |∑ a ∈ Finset.range (X + 1), if a.Coprime q then
          f a * (logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| := by
    have h := abs_add_le (∑ a ∈ Finset.range (X + 1), if a.Coprime q then
        f a * (primesInAPBelow y a q l : ℝ) else 0)
      (-(∑ a ∈ Finset.range (X + 1), if a.Coprime q then
        f a * (logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0))
    simpa [sub_eq_add_neg, abs_neg] using h
  exact h1

/-! ## 主项台阶与 PanChebyshevApprox 的归约 -/

/-- **主项台阶的精确形式**: `f 0 = 0` 时, `panDistributionSum` 的
a = 0 项消失 (它仅当 q = 1 时非零), 且对每个 `1 ≤ a` 用 Chebyshev 恒等式
`π(y; a, q, l) = Σ_{n ≤ y/a, n ≡ a⁻¹l} Λ(n)/log n - PP` 代入, 得到

  `panDistributionSum = Σ_{a ≤ X, (a,q)=1} f(a)·(Λlog_a - li((y:ℝ)/a)/φ(q)) - f(a)·PP_a`.

全部有限代数, 零 sorry; 这是 `PanChebyshevApprox` 归约链的精确出发点. -/
theorem panDistributionSum_eq_mainStep (y X q l : ℕ) (f : ℕ → ℝ) (hf0 : f 0 = 0) :
    panDistributionSum y X q l f =
      ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
          logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) -
        f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q)
      else 0 := by
  rw [panDistributionSum_eq_weighted]
  have h0 : (if (0 : ℕ).Coprime q then f 0 * panDistributionError y 0 q l else 0) = 0 := by
    simp [hf0]
  rw [h0, zero_add]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hcop : a.Coprime q
  · simp only [if_pos hcop]
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have hπ : (primesInAP (y / a) q (natInvMod q a * l % q) : ℝ) =
        apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
          apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) := by
      have h1 := apLogVonMangoldt_eq_primesInAPBelow_inv y a q l (by omega) hcop
      rw [primesInAPBelow_eq_primesInAP_inv y a q l (by omega) hcop] at h1
      linarith
    rw [hπ]
    ring
  · simp only [if_neg hcop]

/-- **开放解析台阶 (Chebyshev 主项吸收, 加权 a-吸收形式)**: 对每个模
`q > 0`、单位剩余类 `l` 与截断参数,

  `|Σ_{(a,q)=1, 1≤a≤X} f(a)·(Λlog(y/a; q, a⁻¹l) − li((y:ℝ)/a)/φ(q))|`
  `+ Σ_{(a,q)=1, 1≤a≤X} |f(a)|·PP(y/a; q, a⁻¹l)`
  `≤ |Σ f(a)·apV1(y/a;...)/log(y/a)| + |Σ f(a)·apV3(y/a;...)/log(y/a)|`
  `+ |Σ f(a)·li((y/a:ℕ):ℝ)/φ(q)|`.

这是 Chebyshev ψ↔π 的等差形式在 a-吸收加权和上的精确剩余: `Λlog` 侧
(`Σ Λ(n)/log n`, 即 `ψ/log`) 被 type I (apV1/log) + type III (apV3/log)
+ 对数积分主项 `li/φ(q)` 控制, 中间项 (apMiddleLog)、小项 (apSmallLog)、
素数次幂修正 (PP) 与 `li` 实/整参数取整差异全部被主项吸收 (Liu 2022 §III
Thm 2; Halberstam--Richert 1974 Ch.10; 经典 Möbius 反演 + PNT 级估计).
这是 `PanChebyshevApprox` 归约后剩下的唯一解析输入; 一旦落地, 由
`PanChebyshevApprox.of_mainStep` 立即得到 `PanChebyshevApprox`. -/
def PanChebyshevMainStep (f : ℕ → ℝ) (u v : ℕ) : Prop :=
  ∀ X q y l : ℕ, 0 < q → l.Coprime q →
    (|∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
          logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| +
      ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0) ≤
      |panPieceSum y X q l f (fun y q l => apV1 y q l u / Real.log (y : ℝ))| +
      |panPieceSum y X q l f (fun y q l => apV3 y q l u v / Real.log (y : ℝ))| +
      |panPieceSum y X q l f (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q)|

/-- **`PanChebyshevApprox` 的归约**: 主项台阶 `PanChebyshevMainStep` (唯一
剩余解析输入) 与 `f 0 = 0` (a = 0 项消失; 见红队定理) 蕴含
`PanChebyshevApprox`. 全部有限代数 (三角不等式, Chebyshev 恒等式代入,
素数次幂修正的 |Σ| ≤ Σ|·| 界) 在此证明, 零 sorry. -/
theorem PanChebyshevApprox.of_mainStep {f : ℕ → ℝ} {u v : ℕ} (hf0 : f 0 = 0)
    (hms : PanChebyshevMainStep f u v) : PanChebyshevApprox f u v := by
  intro X q y l hq hlcop
  let A : ℝ := panPieceSum y X q l f (fun y q l => apV1 y q l u / Real.log (y : ℝ))
  let B : ℝ := panPieceSum y X q l f (fun y q l => apV3 y q l u v / Real.log (y : ℝ))
  let M : ℝ := panPieceSum y X q l f (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q)
  calc
    |panDistributionSum y X q l f|
        = |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
                logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) -
              f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q)
            else 0| := by
          rw [panDistributionSum_eq_mainStep y X q l f hf0]
    _ ≤ |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
                logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| +
          |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0| := by
          have hsplit : (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
                f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
                  logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) -
                f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q)
              else 0) =
              (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
                  f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
                    logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0) -
                (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
                  f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro a ha
            by_cases hcop : a.Coprime q
            · simp only [if_pos hcop]
              try ring
            · simp only [if_neg hcop]
              try ring
          rw [hsplit]
          have htri : |(∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
                  f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
                    logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0) -
              (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
                  f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0)| ≤
              |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
                  f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
                    logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| +
                |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
                  f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0| := by
              have h := abs_add_le (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
                  f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
                    logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0)
                (-(∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
                  f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0))
              simpa [sub_eq_add_neg, abs_neg] using h
          exact htri
    _ ≤ |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
                logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| +
          ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0 := by
          have hpp : |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
                f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0| ≤
              ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
                |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0 := by
            calc
              |∑ a ∈ Finset.Icc 1 X, (if a.Coprime q then
                    f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0)| ≤
                  ∑ a ∈ Finset.Icc 1 X, |(if a.Coprime q then
                    f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0)| := by
                    exact Finset.abs_sum_le_sum_abs
                      (fun a => if a.Coprime q then f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0)
                      (Finset.Icc 1 X)
              _ ≤ ∑ a ∈ Finset.Icc 1 X, (if a.Coprime q then
                    |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0) := by
                    exact Finset.sum_le_sum (fun a ha => by
                      by_cases hcop : a.Coprime q
                      · simp only [if_pos hcop]
                        have hPP : 0 ≤ apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) :=
                          apPrimePowerCorrection_nonneg (y / a) q (natInvMod q a * l % q)
                        rw [abs_mul, abs_of_nonneg hPP]
                      · simp only [if_neg hcop]
                        simp)
          linarith
    _ ≤ |A| + |B| + |M| := by
          simpa [A, B, M] using hms X q y l hq hlcop

/-- **红队: 原 `PanChebyshevApprox` 陈述 (无 `f 0 = 0`) 为假**.
取 `f = 1_{a = 0}`, `X = q = 1`, `y = 2`, `l = 0`: a = 0 项在
`q = 1` 时非零并贡献 `π(2) = 1`, 而 RHS 三个片段和只跑 `1 ≤ a`
(f 在 a ≥ 1 上为 0) 所以都是 0. 经典陈述的 a 从 1 开始; 修复为增加
`f 0 = 0` 假设 (或把 a = 0 项显式并入 RHS). -/
theorem not_PanChebyshevApprox_of_f0 :
    ¬ PanChebyshevApprox (fun a : ℕ => if a = 0 then 1 else 0) 0 0 := by
  intro h
  have hinst := h 1 1 2 0 (by norm_num) (by rw [Nat.coprime_zero_left])
  have hP : ∀ g : ℕ → ℕ → ℕ → ℝ,
      panPieceSum 2 1 1 0 (fun a : ℕ => if a = 0 then 1 else 0) g = 0 := by
    intro g
    unfold panPieceSum
    simp
  have hRHS : |panPieceSum 2 1 1 0 (fun a : ℕ => if a = 0 then 1 else 0)
        (fun y q l => apV1 y q l 0 / Real.log (y : ℝ))| +
      |panPieceSum 2 1 1 0 (fun a : ℕ => if a = 0 then 1 else 0)
        (fun y q l => apV3 y q l 0 0 / Real.log (y : ℝ))| +
      |panPieceSum 2 1 1 0 (fun a : ℕ => if a = 0 then 1 else 0)
        (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q)| = 0 := by
    rw [hP (fun y q l => apV1 y q l 0 / Real.log (y : ℝ)),
        hP (fun y q l => apV3 y q l 0 0 / Real.log (y : ℝ)),
        hP (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q)]
    norm_num
  have hsum : panDistributionSum 2 1 1 0 (fun a : ℕ => if a = 0 then 1 else 0) =
      (primesInAPBelow 2 0 1 0 : ℝ) := by
    unfold panDistributionSum panDistributionError
    simp [logarithmicIntegral, Nat.totient_one]
  have hge1 : 1 ≤ |panDistributionSum 2 1 1 0 (fun a : ℕ => if a = 0 then 1 else 0)| := by
    rw [hsum]
    have hπ : 1 ≤ (primesInAPBelow 2 0 1 0 : ℝ) := by
      unfold primesInAPBelow
      have hmem : 2 ∈ (Finset.range 3).filter (fun p : ℕ => p.Prime ∧ 0 * p ≤ 2 ∧ 0 * p ≡ 0 [MOD 1]) := by
        rw [Finset.mem_filter]
        norm_num
      have hcard0 : 0 < ((Finset.range 3).filter (fun p : ℕ => p.Prime ∧ 0 * p ≤ 2 ∧ 0 * p ≡ 0 [MOD 1])).card :=
        Finset.card_pos.mpr ⟨2, hmem⟩
      exact_mod_cast (Nat.succ_le_of_lt hcard0)
    exact le_trans hπ (le_abs_self _)
  rw [hRHS] at hinst
  have hnot : ¬ |panDistributionSum 2 1 1 0 (fun a : ℕ => if a = 0 then 1 else 0)| ≤ 0 := by
    linarith [hge1]
  exact hnot hinst

/-- **修正第三块 (精确结构定理)**: 由 Section 8 的精确恒等式链,
`panDistributionSum` (π 分布误差) 拆成 type I + type III + **主项吸收块**
`apMiddleLog − apSmallLog + li/φ` + 素数次幂修正:

  |panDistributionSum y X q l f| ≤
    |Σ f(a)·apV1Log(y/a;q,l')| + |Σ f(a)·apV3Log(y/a;q,l')| +
    |Σ f(a)·(apMiddleLog − apSmallLog + li((y:ℝ)/a)/φ(q))| + Σ |f(a)|·PP.

这证实: 纯 `|li/φ|` 第三块是错误形态 (装配后多对数不可吸收, 见
`PanMainTerm.lean` 模块头红队注记), 正确形态是 li 与 Vaughan middle/small
片段合并进**同一个绝对值** (Chebyshev ψ↔π 主项吸收; 经典 Liu 2022 §III
Thm 2 / HR 1974 Ch.10 的 `π(y;q,l)·log y ≈ ΣΛ` 结构). 全部有限代数,
零 sorry. -/
theorem panDistributionSum_abs_le_logPieces_mainBlock (y X q l : ℕ) (f : ℕ → ℝ) (u v : ℕ)
    (hf0 : f 0 = 0) :
    |panDistributionSum y X q l f| ≤
      |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
          f a * apV1Log (y / a) q (natInvMod q a * l % q) u else 0| +
      |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
          f a * apV3Log (y / a) q (natInvMod q a * l % q) u v else 0| +
      |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
          f a * (apMiddleLog (y / a) q (natInvMod q a * l % q) u v -
            apSmallLog (y / a) q (natInvMod q a * l % q) v +
            logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| +
      ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0 := by
  have hmain := panDistributionSum_eq_mainStep y X q l f hf0
  have hlog : (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
          logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) -
        f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0) =
      (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then f a * apV1Log (y / a) q (natInvMod q a * l % q) u else 0) +
      (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then f a * apV3Log (y / a) q (natInvMod q a * l % q) u v else 0) -
      (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
          f a * (apMiddleLog (y / a) q (natInvMod q a * l % q) u v -
            apSmallLog (y / a) q (natInvMod q a * l % q) v +
            logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0) -
      (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
          f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hcop : a.Coprime q
    · simp only [if_pos hcop]
      have hvp := apLogVonMangoldt_eq_logPieces (y / a) q (natInvMod q a * l % q) u v
      rw [hvp]
      ring
    · simp only [if_neg hcop]
      ring
  calc
    |panDistributionSum y X q l f|
        = |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
                logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) -
              f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0| := by
          rw [hmain]
    _ = |(∑ a ∈ Finset.Icc 1 X, if a.Coprime q then f a * apV1Log (y / a) q (natInvMod q a * l % q) u else 0) +
          (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then f a * apV3Log (y / a) q (natInvMod q a * l % q) u v else 0) -
          (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * (apMiddleLog (y / a) q (natInvMod q a * l % q) u v -
                apSmallLog (y / a) q (natInvMod q a * l % q) v +
                logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0) -
          (∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0)| := by
          rw [hlog]
    _ ≤ |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then f a * apV1Log (y / a) q (natInvMod q a * l % q) u else 0| +
          |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then f a * apV3Log (y / a) q (natInvMod q a * l % q) u v else 0| +
          |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * (apMiddleLog (y / a) q (natInvMod q a * l % q) u v -
                apSmallLog (y / a) q (natInvMod q a * l % q) v +
                logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| +
          |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0| := by
          have htri : ∀ x y z w : ℝ, |x + y - z - w| ≤ |x| + |y| + |z| + |w| := by
            intro x y z w
            have h1 : |x + y - z - w| ≤ |x + y| + |z + w| := by
              have h := abs_add_le (x + y) (-(z + w))
              rw [abs_neg] at h
              have heq : x + y - z - w = x + y - (z + w) := by ring
              rw [heq]
              simpa [sub_eq_add_neg] using h
            have h2 : |x + y| ≤ |x| + |y| := abs_add_le x y
            have h3 : |z + w| ≤ |z| + |w| := abs_add_le z w
            linarith
          exact htri _ _ _ _
    _ ≤ |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then f a * apV1Log (y / a) q (natInvMod q a * l % q) u else 0| +
          |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then f a * apV3Log (y / a) q (natInvMod q a * l % q) u v else 0| +
          |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              f a * (apMiddleLog (y / a) q (natInvMod q a * l % q) u v -
                apSmallLog (y / a) q (natInvMod q a * l % q) v +
                logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| +
          ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
              |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0 := by
          have hpp : |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
                f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0| ≤
              ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
                |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0 := by
            calc
              |∑ a ∈ Finset.Icc 1 X, (if a.Coprime q then
                    f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0)| ≤
                  ∑ a ∈ Finset.Icc 1 X, |(if a.Coprime q then
                    f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0)| := by
                    exact Finset.abs_sum_le_sum_abs
                      (fun a => if a.Coprime q then f a * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0)
                      (Finset.Icc 1 X)
              _ ≤ ∑ a ∈ Finset.Icc 1 X, (if a.Coprime q then
                    |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0) := by
                    exact Finset.sum_le_sum (fun a ha => by
                      by_cases hcop : a.Coprime q
                      · simp only [if_pos hcop]
                        have hPP : 0 ≤ apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) :=
                          apPrimePowerCorrection_nonneg (y / a) q (natInvMod q a * l % q)
                        rw [abs_mul, abs_of_nonneg hPP]
                      · simp only [if_neg hcop]
                        simp)
          linarith

/-! ## 9. 红队修正: 第三块必须是 li 吸收 middle/small (issue #44 复查)

`PanChebyshevApprox` 的第三块是纯 `|li/φ(q)|`. 复查确认: 该块装配后是
**多对数量级** — `Σ_{q≤Q} μ²(q)3^ω(q)/φ(q) ≈ (log Q)^{O(1)}` 增长, 而
`panPieceMaxY(li/φ) ≥ (1/φ(q))·Σ_{a≤X}|f(a)|·li(⌊y/a⌋) ≈ y·log X/(φ(q)log y)`,
乘积 ≈ `y·polylog` 不可被 `C·y/log^A y` 压制 (f ≡ 1 即反例). 因此
`PanChebyshevApprox`、`PanVaughanPointwiseSplit` 的第三片段与
`PanMainTermBound`/`PanMainTermSieveBound` (T3) 均需改为主项吸收形态.
精确结构由 `panDistributionSum_abs_le_logPieces_mainBlock` 给出 (零 sorry):
li 与 middle/small 片段合并在同一绝对值内. 下方定义修正陈述与修正 T3'. -/

/-- **修正后的 PanChebyshevApprox (第三块 = li 吸收 middle/small, panPieceSum 形态)**:
第三块为 `|Σ f(a)·(li((y/a:ℕ):ℝ)/φ(q) + apMiddleLog(y/a;q,l',u,v) − apSmallLog(y/a;q,l',v))|`
(主项吸收块), 素数次幂修正显式并入 RHS. 与 `panDistributionSum` 的 li 实参
`(y:ℝ)/a` 的取整差异属于主项台阶 (经典证明以 `li(x) = x/log x + O(x/log²x)`
吸收). 原纯 li 第三块装配后多对数不可吸收, 故本陈述取代
`PanChebyshevApprox`. 需 `f 0 = 0` (a = 0 项, 见红队定理). -/
def PanChebyshevApproxCorrected (f : ℕ → ℝ) (u v : ℕ) : Prop :=
  ∀ X q y l : ℕ, 0 < q → l.Coprime q →
    |panDistributionSum y X q l f| ≤
      |panPieceSum y X q l f (fun y q l => apV1Log y q l u)| +
      |panPieceSum y X q l f (fun y q l => apV3Log y q l u v)| +
      |panPieceSum y X q l f (fun y q l => apMiddleLog y q l u v - apSmallLog y q l v +
          logarithmicIntegral (y : ℝ) / Nat.totient q)| +
      ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0

/-- **修正主项界 T3' (开放解析台阶)**: 主项吸收块 (li 吸收 middle/small) 的
装配级加权界, 取代 `PanMainTermBound` (纯 li 块, 多对数不可吸收).
经典证明 (HR 1974 Ch.10; Liu 2022 §III): Chebyshev ψ↔π 主项关系
`ψ(x;q,l)/log x ≈ li(x)/φ(q)` (主项 `x/φ(q)` 与 li 在 `x/log x` 阶相消),
Vaughan 拆分后各片段光滑部分全局匹配 `x/φ(q)`, 剩余是 PNT 级余项
`O(x/log^A x)` 的界; 该吸收机制是经典解析内容, 保留为本台阶. -/
def PanMainTermAbsorbedBound (x f : ℕ → ℝ) (u v : ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
    ∀ X : ℕ, x₀ ≤ X →
      ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panPieceMaxY X q (Nat.floor (x X)) f
            (fun y q l => apMiddleLog y q l u v - apSmallLog y q l v +
              logarithmicIntegral (y : ℝ) / Nat.totient q) ≤
        C * x X / (log (x X)) ^ A

/-! ## 10. 主项台阶的精确拆解与红队 (issue #44 剩余核心)

### 数学结论

`PanChebyshevMainStep` (:724) 是 `PanChebyshevApprox` 归约后唯一的开放解析台阶.
本节给出它的**精确拆解**: (1) 零 sorry 的精确结构定理
`panChebyshevMainStepLHS_abs_le_corrected`, 把它的 LHS 拆成
type I (`apV1Log`) + type III (`apV3Log`) + **主项吸收块**
`|Σ f(a)·(apMiddleLog − apSmallLog + li((y:ℝ)/a)/φ(q))|` + 素数次幂修正;
(2) 零 sorry 的红队定理 `not_PanChebyshevMainStep`: 原陈述 (∀ f, ∀ u v
的逐点不等式) **为假**, 反例显式构造.

### 论证 (为什么正确形态如此)

由 `apLogVonMangoldt_eq_logPieces` (:585) 逐 a 代入:

  Λlog(y/a;q,a⁻¹l) = V1Log − MiddleLog + V3Log + SmallLog,

于是 (a 加权和, (a,q)=1, 1≤a≤X):

  Σ f(a)·(Λlog_a − li((y:ℝ)/a)/φ(q))
    = Σ f(a)·V1Log_a + Σ f(a)·V3Log_a − Σ f(a)·(MiddleLog_a − SmallLog_a + li_a/φ(q)),

三角不等式给出 `panChebyshevMainStepLHS_abs_le_corrected` (零 sorry):
LHS(PanChebyshevMainStep) ≤ |Σ f·V1Log| + |Σ f·V3Log| + |吸收块| + Σ|f|·PP.
这与 `panDistributionSum_abs_le_logPieces_mainBlock` (:882) 的 π 侧形态完全一致,
说明 Chebyshev ψ↔π 之后主项吸收的**正确点式形状**是 li 与 middle/small 在
同一个绝对值内 (Liu 2022 §III Thm 2; HR 1974 Ch.10), 而非纯 `|li/φ|` 块.

**为什么 middle/small/PP/取整能被主项吸收** (解析级论证, 非本文件范围):

1. **小项 S**: `SmallLog_a = π(min(y/a,v); q, a⁻¹l) + PP(≤v)`
   (`apLogVonMangoldt_eq_primesInAP_add_pp`). 当 `v = o(y/a)` 时
   `π(min(y/a,v)) ≈ li(min(y/a,v))/φ(q) = o(li(y/a)/φ(q))`; 当 `y/a ≤ v` 时
   `SmallLog_a = π(y/a;q,l') + PP ≈ li(y/a)/φ(q)·(1+o(1))` (等差 PNT).
2. **中间项 M**: Möbius 反演后 `MiddleLog_a ≈ (y/a/φ(q))·Σ_{d≤u} μ(d)/d·(1+o(1))`,
   关键 **Möbius 尾部** `Σ_{d≤u} μ(d)/d → 0` (PNT 等价) 使主项为 `o(li)`.
3. **素数次幂修正**: `PP(y/a) = O(√(y/a)·log(y/a)) = o(li(y/a))`.
4. **取整差异**: LHS 用实参数 `li((y:ℝ)/a)`, 片段用整参数 `li((y/a:ℕ):ℝ)`;
   差 `|li_ℝ − li_ℤ| ≤ 3/log(y/a)` (li(x) = x/log x), 相对 li 是 `o(1)`.

即吸收块 ≈ `li_ℝ/φ(q)·(1 + o(1))`; 逐 a 加权 (|f| ≤ 1 + Chen 权重) 后
`o(li)` 余项被筛主项 (BRG 相减) 吸收成装配级 `O(x/log^A x)` — 这正是
`PanMainTermAbsorbedBound` (:1019), 是**开放解析台阶**.

### 为什么原 `PanChebyshevMainStep` 为假 (红队)

原 RHS 第三块是纯 `|Σ f(a)·li((y/a:ℕ):ℝ)/φ(q)|`, 对任意 f 无 "余量" 吸收
middle/small/PP 的 L1 项: 取 `f(1) = li(⌊y/2⌋)`, `f(2) = −li(⌊y⌋)` (X=2, q=1)
使 `Σ f(a)·li_ℤ = 0` 而 `Σ|f|·PP > 0`; 取 `u ≥ y` 使 V1 = Λlog、V3 = 0;
y = 4 时逐项计算 (本文件零 sorry 完成) 得 LHS = 2c, RHS = c·log3/(2log2) < 2c
(c = 2/log2, 因 log16 > log3). 结论: 原陈述需修正为
`panChebyshevMainStepLHS_abs_le_corrected` 的形态 + 装配级 `PanMainTermAbsorbedBound`.

### 需要的显式解析子台阶 (Prop, 不引入公理)

1. **PNT-AP / Siegel–Walfisz 级**: `π(x;q,l) = li(x)/φ(q) + O(x/(φ(q)·log^A x))`
   对 `q ≤ log^B x` 一致 — 仓库未落地 (现 BombieriVinogradov.lean 的 `bombieri_vinogradov`
   是逐参数的平凡陈述, 非真 BV); 需要新材料 (等差 PNT / Siegel–Walfisz).
2. **Möbius 尾部**: `|Σ_{d≤u} μ(d)/d| = O(1/log u)` (PNT 推论) — 仓库未落地.
3. **装配级主项吸收**: `PanMainTermAbsorbedBound` (已定义 :1019) — 开放.
4. **取整引理**: `|li((y:ℝ)/a) − li((y/a:ℕ):ℝ)| ≤ 3/log(y/a)` — 在 li = x/log x
   定义下为纯实分析, 可证 (不在本文件).
-/

/-- 对数小常数: `0 < log 2`. -/
private lemma log_two_pos : 0 < Real.log 2 :=
  Real.log_pos (by norm_num : (1 : ℝ) < 2)

/-- 对数小常数: `0 < log 3`. -/
private lemma log_three_pos : 0 < Real.log 3 :=
  Real.log_pos (by norm_num : (1 : ℝ) < 3)

/-- 对数小常数: `log 2 ≠ 0`. -/
private lemma log_two_ne_zero : Real.log 2 ≠ 0 := log_two_pos.ne'

/-- 对数小常数: `2·log 2 ≠ 0`. -/
private lemma two_mul_log_two_ne_zero : 2 * Real.log 2 ≠ 0 :=
  mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) log_two_ne_zero

/-- `log 4 = 2·log 2`. -/
private lemma log_four_eq_two_log_two : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
  norm_num

/-- `Λ 0 = 0` (镜像 PanTypeIIBoundAudit, 避免新增 import). -/
private lemma vonMangoldt_zero : Λ 0 = 0 := by
  rw [ArithmeticFunction.vonMangoldt_apply]
  simp [not_isPrimePow_zero]

/-- `Λ 4 = log 2` (4 = 2², `vonMangoldt_apply_pow`). -/
private lemma vonMangoldt_four : Λ 4 = Real.log 2 := by
  have h := ArithmeticFunction.vonMangoldt_apply_pow (n := 2) (k := 2) (by norm_num : (2 : ℕ) ≠ 0)
  norm_num at h
  rw [h]
  exact ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : (2 : ℕ).Prime)

/-- `vaughanFirst n u = Λ n` 当 `u ≥ n` (Vaughan 三段恒等式 + 空项). -/
private lemma vaughanFirst_eq_vonMangoldt_of_ge {n u : ℕ} (hu : n ≤ u) :
    vaughanFirst n u = Λ n := by
  have h := vaughanIdentity n u 0
  have h2 : vaughanSecond n u 0 = 0 := by
    unfold vaughanSecond
    apply Finset.sum_eq_zero
    intro d hd
    apply Finset.sum_eq_zero
    intro e he
    exfalso
    have he' : e ∈ (n / d).divisors := (Finset.mem_filter.mp he).1
    have hmd : 0 < n / d := Nat.pos_of_ne_zero (Nat.mem_divisors.mp he').2
    have hepos : 0 < e := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp he').1 hmd
    have hele : e ≤ 0 := (Finset.mem_filter.mp he).2
    omega
  have h3 : vaughanThird n u 0 = 0 := by
    unfold vaughanThird
    by_cases hn : n = 0
    · subst n
      simp [Nat.divisors_zero]
    · apply Finset.sum_eq_zero
      intro d hd
      exfalso
      have hd' : d ∈ n.divisors := (Finset.mem_filter.mp hd).1
      have hdg : u < d := (Finset.mem_filter.mp hd).2
      have hdvd : d ∣ n := (Nat.mem_divisors.mp hd').1
      have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
      omega
  linarith

/-- `vaughanThird n u v = 0` 当 `u ≥ n` (外滤子空). -/
private lemma vaughanThird_zero_of_u_ge {n u v : ℕ} (hu : n ≤ u) :
    vaughanThird n u v = 0 := by
  unfold vaughanThird
  by_cases hn : n = 0
  · subst n
    simp [Nat.divisors_zero]
  · apply Finset.sum_eq_zero
    intro d hd
    exfalso
    have hd' : d ∈ n.divisors := (Finset.mem_filter.mp hd).1
    have hdg : u < d := (Finset.mem_filter.mp hd).2
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd').1
    have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
    omega

/-- 小常数: `li(2) = 2/log 2` (工作定义 li x = x/log x). -/
private lemma logIntegral_two : logarithmicIntegral (2 : ℝ) = (2 : ℝ) / Real.log 2 := by
  simp [logarithmicIntegral]

/-- 小常数: `li(4) = 2/log 2` (= li(2), 因 4/log4 = 2/log2). -/
private lemma logIntegral_four : logarithmicIntegral (4 : ℝ) = (2 : ℝ) / Real.log 2 := by
  simp [logarithmicIntegral]
  rw [log_four_eq_two_log_two]
  field_simp [log_two_ne_zero, two_mul_log_two_ne_zero] <;> ring

/-- 小常数: `apLogVonMangoldt 2 1 0 = 1` (素数 2 贡献 1). -/
private lemma apLogVonMangoldt_two : apLogVonMangoldt 2 1 0 = 1 := by
  unfold apLogVonMangoldt
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp [vonMangoldt_zero, ArithmeticFunction.vonMangoldt_apply_one,
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : (2 : ℕ).Prime),
    log_two_ne_zero] <;> norm_num

/-- 小常数: `apLogVonMangoldt 4 1 0 = 5/2` (素数 2,3 各 1, 4 贡献 1/2). -/
private lemma apLogVonMangoldt_four : apLogVonMangoldt 4 1 0 = (5 : ℝ) / 2 := by
  unfold apLogVonMangoldt
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  have hdiv : Real.log 2 / (2 * Real.log 2) = (1 : ℝ) / 2 := by
    field_simp [log_two_ne_zero, two_mul_log_two_ne_zero] <;> ring
  simp [vonMangoldt_zero, ArithmeticFunction.vonMangoldt_apply_one,
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : (2 : ℕ).Prime),
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : (3 : ℕ).Prime),
    vonMangoldt_four, log_four_eq_two_log_two, log_two_ne_zero, hdiv] <;> norm_num

/-- 小常数: `apPrimePowerCorrection 2 1 0 = 0`. -/
private lemma apPrimePowerCorrection_two : apPrimePowerCorrection 2 1 0 = 0 := by
  unfold apPrimePowerCorrection
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp [vonMangoldt_zero, ArithmeticFunction.vonMangoldt_apply_one, log_two_ne_zero]
    <;> norm_num

/-- 小常数: `apPrimePowerCorrection 4 1 0 = 1/2` (4 = 2²). -/
private lemma apPrimePowerCorrection_four : apPrimePowerCorrection 4 1 0 = (1 : ℝ) / 2 := by
  unfold apPrimePowerCorrection
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  have hdiv : Real.log 2 / (2 * Real.log 2) = (1 : ℝ) / 2 := by
    field_simp [log_two_ne_zero, two_mul_log_two_ne_zero] <;> ring
  simp [vonMangoldt_zero, ArithmeticFunction.vonMangoldt_apply_one, vonMangoldt_four,
    log_four_eq_two_log_two, log_two_ne_zero, hdiv] <;> norm_num

/-- 小常数: `apV1 2 1 0 4 = log 2` (u = 4 ≥ n 时 vaughanFirst = Λ). -/
private lemma apV1_two : apV1 2 1 0 4 = Real.log 2 := by
  unfold apV1
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have h0 : vaughanFirst 0 4 = Λ 0 := vaughanFirst_eq_vonMangoldt_of_ge (by norm_num : (0 : ℕ) ≤ 4)
  have h1 : vaughanFirst 1 4 = Λ 1 := vaughanFirst_eq_vonMangoldt_of_ge (by norm_num : (1 : ℕ) ≤ 4)
  have h2 : vaughanFirst 2 4 = Λ 2 := vaughanFirst_eq_vonMangoldt_of_ge (by norm_num : (2 : ℕ) ≤ 4)
  simp [h0, h1, h2, vonMangoldt_zero, ArithmeticFunction.vonMangoldt_apply_one,
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : (2 : ℕ).Prime)] <;> norm_num

/-- 小常数: `apV1 4 1 0 4 = 2·log 2 + log 3` (= ψ(4)). -/
private lemma apV1_four : apV1 4 1 0 4 = 2 * Real.log 2 + Real.log 3 := by
  unfold apV1
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  have h0 : vaughanFirst 0 4 = Λ 0 := vaughanFirst_eq_vonMangoldt_of_ge (by norm_num : (0 : ℕ) ≤ 4)
  have h1 : vaughanFirst 1 4 = Λ 1 := vaughanFirst_eq_vonMangoldt_of_ge (by norm_num : (1 : ℕ) ≤ 4)
  have h2 : vaughanFirst 2 4 = Λ 2 := vaughanFirst_eq_vonMangoldt_of_ge (by norm_num : (2 : ℕ) ≤ 4)
  have h3 : vaughanFirst 3 4 = Λ 3 := vaughanFirst_eq_vonMangoldt_of_ge (by norm_num : (3 : ℕ) ≤ 4)
  have h4 : vaughanFirst 4 4 = Λ 4 := vaughanFirst_eq_vonMangoldt_of_ge (by norm_num : (4 : ℕ) ≤ 4)
  simp [h0, h1, h2, h3, h4, vonMangoldt_zero, ArithmeticFunction.vonMangoldt_apply_one,
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : (2 : ℕ).Prime),
    ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : (3 : ℕ).Prime),
    vonMangoldt_four] <;> norm_num <;> ring_nf

/-- 小常数: `apV3 2 1 0 4 0 = 0` (u = 4 ≥ n). -/
private lemma apV3_two : apV3 2 1 0 4 0 = 0 := by
  unfold apV3
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have h0 : vaughanThird 0 4 0 = 0 := vaughanThird_zero_of_u_ge (by norm_num : (0 : ℕ) ≤ 4)
  have h1 : vaughanThird 1 4 0 = 0 := vaughanThird_zero_of_u_ge (by norm_num : (1 : ℕ) ≤ 4)
  have h2 : vaughanThird 2 4 0 = 0 := vaughanThird_zero_of_u_ge (by norm_num : (2 : ℕ) ≤ 4)
  simp [h0, h1, h2] <;> norm_num

/-- 小常数: `apV3 4 1 0 4 0 = 0`. -/
private lemma apV3_four : apV3 4 1 0 4 0 = 0 := by
  unfold apV3
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  have h0 : vaughanThird 0 4 0 = 0 := vaughanThird_zero_of_u_ge (by norm_num : (0 : ℕ) ≤ 4)
  have h1 : vaughanThird 1 4 0 = 0 := vaughanThird_zero_of_u_ge (by norm_num : (1 : ℕ) ≤ 4)
  have h2 : vaughanThird 2 4 0 = 0 := vaughanThird_zero_of_u_ge (by norm_num : (2 : ℕ) ≤ 4)
  have h3 : vaughanThird 3 4 0 = 0 := vaughanThird_zero_of_u_ge (by norm_num : (3 : ℕ) ≤ 4)
  have h4 : vaughanThird 4 4 0 = 0 := vaughanThird_zero_of_u_ge (by norm_num : (4 : ℕ) ≤ 4)
  simp [h0, h1, h2, h3, h4] <;> norm_num

/-- 有限集 `Icc 1 2` 上的和退化为两点和. -/
private lemma sum_Icc_1_2 (g : ℕ → ℝ) :
    (∑ a ∈ Finset.Icc 1 2, g a) = g 1 + g 2 := by
  rw [show Finset.Icc (1 : ℕ) 2 = ({1, 2} : Finset ℕ) by decide]
  norm_num [Finset.sum_insert, Finset.sum_singleton] <;> ring

/-- **主项台阶 LHS 的精确拆解 (零 sorry, 正确形态)**: 对任意 `f u v`,
`PanChebyshevMainStep` 的 LHS 被 type I + type III + 主项吸收块
(li 与 middle/small 在同一绝对值内) + 素数次幂修正控制:

  `|Σ f(Λlog − li_ℝ/φ)| + Σ|f|·PP ≤ |Σ f·V1Log| + |Σ f·V3Log|
      + |Σ f·(MiddleLog − SmallLog + li_ℝ/φ)| + Σ|f|·PP`.

由 `apLogVonMangoldt_eq_logPieces` 逐 a 代入 + 三角不等式; 纯有限代数. -/
theorem panChebyshevMainStepLHS_abs_le_corrected (y X q l : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    (|∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
          logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| +
      ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0) ≤
      |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
          f a * apV1Log (y / a) q (natInvMod q a * l % q) u else 0| +
      |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
          f a * apV3Log (y / a) q (natInvMod q a * l % q) u v else 0| +
      |∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
          f a * (apMiddleLog (y / a) q (natInvMod q a * l % q) u v -
            apSmallLog (y / a) q (natInvMod q a * l % q) v +
            logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| +
      ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0 := by
  let A : ℝ := ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
      f a * apV1Log (y / a) q (natInvMod q a * l % q) u else 0
  let B : ℝ := ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
      f a * apV3Log (y / a) q (natInvMod q a * l % q) u v else 0
  let C : ℝ := ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
      f a * (apMiddleLog (y / a) q (natInvMod q a * l % q) u v -
        apSmallLog (y / a) q (natInvMod q a * l % q) v +
        logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0
  let P : ℝ := ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
      |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0
  let S : ℝ := ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
      f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
        logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0
  have hsplit : S = A + B - C := by
    dsimp [S, A, B, C]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hcop : a.Coprime q
    · simp only [if_pos hcop]
      have hvp := apLogVonMangoldt_eq_logPieces (y / a) q (natInvMod q a * l % q) u v
      rw [hvp]
      ring
    · simp only [if_neg hcop]
      ring
  have htri : ∀ x y z : ℝ, |x + y - z| ≤ |x| + |y| + |z| := by
    intro x y z
    have h1 : |x + y - z| ≤ |x + y| + |z| := by
      have h := abs_add_le (x + y) (-z)
      rw [abs_neg] at h
      simpa [sub_eq_add_neg] using h
    have h2 : |x + y| ≤ |x| + |y| := abs_add_le x y
    linarith
  calc
    (|∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        f a * (apLogVonMangoldt (y / a) q (natInvMod q a * l % q) -
          logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) else 0| +
      ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then
        |f a| * apPrimePowerCorrection (y / a) q (natInvMod q a * l % q) else 0)
        = |S| + P := by
          simp [S, P]
    _ ≤ (|A| + |B| + |C|) + P := by
          have htri' : |A + B - C| ≤ |A| + |B| + |C| := htri A B C
          have hS : |S| = |A + B - C| := by rw [hsplit]
          linarith
    _ = |A| + |B| + |C| + P := by ring

/-- **红队: 原 `PanChebyshevMainStep` 陈述 (∀ f, ∀ u v) 为假**.
反例: X = 2, q = 1, y = 4, l = 0, u = 4, v = 0,
`f(1) = c = 2/log 2`, `f(2) = −c` (其余 0). 此时 `u ≥ y` 使 type I = Λlog、
type III = 0; `li(4) = li(2) = c` 使 RHS 第三块 `Σ f·li_ℤ = 0`;
逐项计算: LHS = |c·3/2| + c·1/2 = 2c, RHS = |c·((2log2+log3)/(2log2) − 1)| = c·log3/(2log2),
而 `2c > c·log3/(2log2)` 因 `log16 > log3`. 全部零 sorry. -/
theorem not_PanChebyshevMainStep :
    ¬ PanChebyshevMainStep (fun a : ℕ =>
        if a = 1 then (2 : ℝ) / Real.log 2
        else if a = 2 then -((2 : ℝ) / Real.log 2) else 0) 4 0 := by
  intro h
  let c : ℝ := (2 : ℝ) / Real.log 2
  let f : ℕ → ℝ := fun a => if a = 1 then c else if a = 2 then -c else 0
  have hcpos : 0 < c := by
    dsimp [c]
    exact div_pos (by norm_num) log_two_pos
  have hinst := h 2 1 4 0 (by norm_num) (by rw [Nat.coprime_zero_left])
  change (|∑ a ∈ Finset.Icc 1 2, if a.Coprime 1 then
        f a * (apLogVonMangoldt (4 / a) 1 (natInvMod 1 a * 0 % 1) -
          logarithmicIntegral ((4 : ℝ) / a) / Nat.totient 1) else 0| +
      ∑ a ∈ Finset.Icc 1 2, if a.Coprime 1 then
        |f a| * apPrimePowerCorrection (4 / a) 1 (natInvMod 1 a * 0 % 1) else 0) ≤
      |panPieceSum 4 2 1 0 f (fun y q l => apV1 y q l 4 / Real.log (y : ℝ))| +
      |panPieceSum 4 2 1 0 f (fun y q l => apV3 y q l 4 0 / Real.log (y : ℝ))| +
      |panPieceSum 4 2 1 0 f (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q)| at hinst
  have hS1 : (∑ a ∈ Finset.Icc 1 2, if a.Coprime 1 then
        f a * (apLogVonMangoldt (4 / a) 1 (natInvMod 1 a * 0 % 1) -
          logarithmicIntegral ((4 : ℝ) / a) / Nat.totient 1) else 0) =
      c * (3 : ℝ) / 2 := by
    rw [sum_Icc_1_2 (fun a : ℕ => if a.Coprime 1 then
        f a * (apLogVonMangoldt (4 / a) 1 (natInvMod 1 a * 0 % 1) -
          logarithmicIntegral ((4 : ℝ) / a) / Nat.totient 1) else 0)]
    norm_num [f, Nat.totient_one]
    rw [apLogVonMangoldt_four, apLogVonMangoldt_two, logIntegral_four, logIntegral_two]
    ring_nf
  have hS1abs : |∑ a ∈ Finset.Icc 1 2, if a.Coprime 1 then
        f a * (apLogVonMangoldt (4 / a) 1 (natInvMod 1 a * 0 % 1) -
          logarithmicIntegral ((4 : ℝ) / a) / Nat.totient 1) else 0| =
      c * (3 : ℝ) / 2 := by
    rw [hS1]
    exact abs_of_pos (div_pos (mul_pos hcpos (by norm_num : (0 : ℝ) < 3)) (by norm_num : (0 : ℝ) < 2))
  have hS2 : (∑ a ∈ Finset.Icc 1 2, if a.Coprime 1 then
        |f a| * apPrimePowerCorrection (4 / a) 1 (natInvMod 1 a * 0 % 1) else 0) =
      c * (1 : ℝ) / 2 := by
    rw [sum_Icc_1_2 (fun a : ℕ => if a.Coprime 1 then
        |f a| * apPrimePowerCorrection (4 / a) 1 (natInvMod 1 a * 0 % 1) else 0)]
    norm_num [f, Nat.totient_one]
    rw [apPrimePowerCorrection_four, apPrimePowerCorrection_two]
    simp [abs_of_pos hcpos, abs_neg] <;> ring_nf
  have hT1 : panPieceSum 4 2 1 0 f (fun y q l => apV1 y q l 4 / Real.log (y : ℝ)) =
      c * Real.log 3 / (2 * Real.log 2) := by
    unfold panPieceSum
    rw [sum_Icc_1_2 (fun a : ℕ => if a.Coprime 1 then
        f a * (apV1 (4 / a) 1 (natInvMod 1 a * 0 % 1) 4 / Real.log ((4 / a : ℕ) : ℝ)) else 0)]
    norm_num [f]
    rw [apV1_four, apV1_two, log_four_eq_two_log_two]
    have hdiv1 : Real.log 2 / Real.log 2 = 1 := div_self log_two_ne_zero
    have hsplit : (2 * Real.log 2 + Real.log 3) / (2 * Real.log 2) =
        1 + Real.log 3 / (2 * Real.log 2) := by
      field_simp [two_mul_log_two_ne_zero] <;> ring
    rw [hdiv1, hsplit]
    ring
  have hT1pos : 0 < c * Real.log 3 / (2 * Real.log 2) := by
    exact div_pos (mul_pos hcpos log_three_pos) (mul_pos (by norm_num) log_two_pos)
  have hT1abs : |panPieceSum 4 2 1 0 f (fun y q l => apV1 y q l 4 / Real.log (y : ℝ))| =
      c * Real.log 3 / (2 * Real.log 2) := by
    rw [hT1]
    exact abs_of_pos hT1pos
  have hT2 : panPieceSum 4 2 1 0 f (fun y q l => apV3 y q l 4 0 / Real.log (y : ℝ)) = 0 := by
    unfold panPieceSum
    rw [sum_Icc_1_2 (fun a : ℕ => if a.Coprime 1 then
        f a * (apV3 (4 / a) 1 (natInvMod 1 a * 0 % 1) 4 0 / Real.log ((4 / a : ℕ) : ℝ)) else 0)]
    norm_num [f]
    rw [apV3_four, apV3_two]
    simp
  have hT3 : panPieceSum 4 2 1 0 f
      (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q) = 0 := by
    unfold panPieceSum
    rw [sum_Icc_1_2 (fun a : ℕ => if a.Coprime 1 then
        f a * (logarithmicIntegral ((4 / a : ℕ) : ℝ) / Nat.totient 1) else 0)]
    norm_num [f, Nat.totient_one]
    rw [logIntegral_four, logIntegral_two]
    simp <;> ring
  have hLHS : (|∑ a ∈ Finset.Icc 1 2, if a.Coprime 1 then
        f a * (apLogVonMangoldt (4 / a) 1 (natInvMod 1 a * 0 % 1) -
          logarithmicIntegral ((4 : ℝ) / a) / Nat.totient 1) else 0| +
      ∑ a ∈ Finset.Icc 1 2, if a.Coprime 1 then
        |f a| * apPrimePowerCorrection (4 / a) 1 (natInvMod 1 a * 0 % 1) else 0) = c * 2 := by
    rw [hS1abs, hS2]
    ring_nf
  have hRHS : |panPieceSum 4 2 1 0 f (fun y q l => apV1 y q l 4 / Real.log (y : ℝ))| +
      |panPieceSum 4 2 1 0 f (fun y q l => apV3 y q l 4 0 / Real.log (y : ℝ))| +
      |panPieceSum 4 2 1 0 f (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q)| =
      c * Real.log 3 / (2 * Real.log 2) := by
    rw [hT1abs, hT2, hT3]
    simp
  rw [hLHS, hRHS] at hinst
  have hlt : c * Real.log 3 / (2 * Real.log 2) < c * 2 := by
    have hlog16 : Real.log (16 : ℝ) = (4 : ℝ) * Real.log 2 := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, Real.log_pow]
      norm_num
    have h34 : Real.log 3 < (4 : ℝ) * Real.log 2 := by
      have hltl := Real.log_lt_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) < 16)
      rw [hlog16] at hltl
      exact hltl
    have h2log : 0 < 2 * Real.log 2 := mul_pos (by norm_num) log_two_pos
    have hfrac : Real.log 3 / (2 * Real.log 2) < (2 : ℝ) := by
      have hd := div_lt_div_of_pos_right h34 h2log
      have hcancel : (4 * Real.log 2) / (2 * Real.log 2) = (2 : ℝ) := by
        field_simp [log_two_ne_zero, two_mul_log_two_ne_zero] <;> ring
      linarith
    calc
      c * Real.log 3 / (2 * Real.log 2) = c * (Real.log 3 / (2 * Real.log 2)) := by ring
      _ < c * 2 := mul_lt_mul_of_pos_left hfrac hcpos
  linarith


end

end AnalyticNumberTheory.Sieve
