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

2. **解析台阶 (Prop 封装, 不引入公理, 不 sorry)**: `PanChebyshevApprox` -
   逐 (y,l) 点式拆分, 即 "Λ-计数 → 素数计数" 的 Chebyshev ψ↔π 转换与
   middle/small 主项吸收进 li 的 PNT 级内容 (Liu 2022 §III Thm 2;
   Halberstam--Richert 1974 Ch.10; 经典 Chebyshev: `ψ(y) = Σ_{n≤y} Λ(n) ≈
   π(y)·log y`).

3. **max 组合 (零 sorry)**: `panMaxL_le_pieces_sum` / `panMaxY_le_pieces_sum`
   把逐 (y,l) 点式拆分提升为双 max 形式
   (`max_{y'≤y} max_l |·| ≤ 三片段 max 之和`), 从而
   `PanVaughanPointwiseSplit.of_chebyshevApprox`:
   `PanChebyshevApprox ⇒ PanVaughanPointwiseSplit`.

装配 (PanAssembly.lean) 消费 `PanVaughanPointwiseSplit` 作为 `hsplit`,
与 `PanLogEventuallyLarge` 一起经 `PanVaughanSplit.of_analyticInputs`
给出 `PanMeanValueUniform` 的完整证明.
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
不 sorry; 以 Prop 封装, 供后续落地). -/
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

end

end AnalyticNumberTheory.Sieve
