/-
! # AnalyticNumberTheory.Sieve.PanMeanValueBody

## 加权 Pan 均值定理的证明主体 (ant #15, 分支 research/pan-mean-value-body)

本模块推进 `PanMeanValueUniform` (见 `WeightedPan.lean`) 的证明, 按 Liu 2022
§II--§III 的经典路线:

```text
a-吸收 (Liu §II)            -- 本文件 Section 1-2: 互素缩放 `a` 被吸收进剩余类,
                               `π(y; a, q, l) = π(y/a; q, l·a⁻¹)`, 使 Pan 对象
                               归结为普通等差素数计数的加权和
max 脚手架                  -- 本文件 Section 3: `panMaxL`/`panMaxY` 的
                               非负性与 "max ≤ 求和" 界 (装配期去 max 用)
```

**Section 1** 建立模 `q` 逆剩余类 `natInvMod q a` 与同余消去引理
`modEq_mul_left_inv_iff`: 对 `(a,q) = 1`,

  `a·p ≡ l [MOD q]  ⟺  p ≡ natInvMod q a · l [MOD q]`.

**Section 2** 给出 Liu §II 的精确归约:

  `primesInAPBelow y a q l = primesInAP (y / a) q (natInvMod q a · l % q)`
  (计数在 `p ↦ p` 恒等映射下成立: 条件 `a·p ≤ y` 等价于 `p ≤ y/a`,
  同余条件由 Section 1 替换), 从而

  `panDistributionError y a q l =
     (primesInAP (y/a) q (natInvMod q a · l % q)) - li(y/a)/φ(q)`

  并把 `panDistributionSum` 写成经典加权形式 (Liu Thm 2 的内和):

  `Σ_{(a,q)=1, a ≤ X} f(a)·Δ(y; a, q, l)
     = Σ_{1 ≤ a ≤ X} [a.Coprime q] · f(a) ·
         (π(y/a; q, l·a⁻¹) − li(y/a)/φ(q)) + O(a=0 项)`.

后续台阶 (本仓库已有装置): 大筛在 Farey 点上的均值定理
(`LargeSieve.Multiplicative.largeSieveRationalPoints`), 模 q 特征大筛
(`characterSieveModulus_le`), Vaughan 恒等式 (`Sieve.VaughanIdentity`),
以及 `3^{ω(q)} = Σ_{d|q} 2^{ω(d)}` 权重打包 (`WeightedPan`).

**T1 进展 (ant #15, PR #31)**: type I 加权界已被 §5 的有限代数链精确归约:
`PanTypeIWeightedBound` 从开放引理 `PanTypeICharacterMeanValue` (特征均值界,
§5) 推出 (见 `PanTypeIWeightedBound.of_characterMeanValue`). 尚未落地:
type II 界 (T2) 与最终装配 (见 `PAN_PROOF_ATLAS.md` 的路线表, 状态标注).
-/

import AnalyticNumberTheory.Sieve.WeightedPan
import AnalyticNumberTheory.Sieve.VaughanIdentity
import Mathlib.Data.ZMod.Basic
import AnalyticNumberTheory.LargeSieve.CharacterIndicators
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.GroupTheory.Exponent
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic

namespace AnalyticNumberTheory.Sieve

open Finset Real

open scoped Classical
open scoped ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.omega

/-! ## 1. 模 q 的逆剩余类与同余消去 -/

/-- 模 `q` 的逆剩余类: `(a,q) = 1` 时取 `ZMod q` 中 `a` 的逆元的自然代表
(`ZMod.val` 是最小非负代表, 模 0 时为绝对值), 它满足 `a·b ≡ 1 [MOD q]`;
否则取 0 (仅在互素假设下使用). -/
noncomputable def natInvMod (q a : ℕ) : ℕ :=
  if _h : a.Coprime q then (a⁻¹ : ZMod q).val else 0

/-- `natInvMod` 的定义性质: `(a,q) = 1` 时 `a · natInvMod q a % q = 1 % q`
(即 `a · natInvMod q a ≡ 1 [MOD q]`; 对所有 `q` 成立, `q = 0, 1` 时平凡). -/
theorem natInvMod_spec {q a : ℕ} (hcop : a.Coprime q) :
    a * natInvMod q a % q = 1 % q := by
  unfold natInvMod
  rw [dif_pos hcop]
  have hz : ((a * (a⁻¹ : ZMod q).val : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
    rw [Nat.cast_mul]
    simpa using (ZMod.mul_val_inv hcop)
  exact (ZMod.natCast_eq_natCast_iff (a := a * (a⁻¹ : ZMod q).val) (b := 1) (c := q)).mp hz

/-- `natInvMod` 的同余形式: `a · natInvMod q a ≡ 1 [MOD q]` (对所有 `q` 成立,
`q = 0, 1` 时平凡). -/
theorem natInvMod_congr {q a : ℕ} (hcop : a.Coprime q) :
    a * natInvMod q a ≡ 1 [MOD q] := by
  rw [Nat.ModEq]
  exact natInvMod_spec hcop

/-- **同余消去 (互素乘法)**: 若 `a·b ≡ 1 [MOD q]`, 则

  `a·p ≡ l [MOD q]  ⟺  p ≡ b·l [MOD q]`.

这是 Liu §II "a-吸收" 的同余核心: 把 `(a,q) = 1` 的缩放乘到素数 `p` 上的
同余条件改写为 `p` 的剩余类条件. -/
theorem modEq_mul_left_inv_iff {q a p l b : ℕ} (hb : a * b ≡ 1 [MOD q]) :
    (a * p ≡ l [MOD q]) ↔ (p ≡ b * l [MOD q]) := by
  constructor
  · intro hcong
    have h1 : b * (a * p) ≡ b * l [MOD q] := hcong.mul_left b
    have hba : b * a ≡ 1 [MOD q] := by simpa [Nat.mul_comm] using hb
    have hp : (b * a) * p ≡ 1 * p [MOD q] := hba.mul_right p
    have h2 : b * (a * p) ≡ p [MOD q] := by
      simpa [Nat.mul_assoc, one_mul] using hp
    exact h2.symm.trans h1
  · intro hcong
    have h1 : a * p ≡ a * (b * l) [MOD q] := hcong.mul_left a
    have h2 : a * (b * l) ≡ l [MOD q] := by
      simpa [Nat.mul_assoc, one_mul] using hb.mul_right l
    exact h1.trans h2

/-! ## 2. Liu §II 的 a-吸收: 缩放计数与加权分布误差 -/

/-- **缩放计数 = 普通等差计数** (Liu §II): 对 `(a,q) = 1, a ≥ 1`,

  `π(y; a, q, l) = π(y/a; q, l·a⁻¹)`,

即 `#{p : a·p ≤ y, a·p ≡ l [MOD q]} = #{p : p ≤ y/a, p ≡ l·a⁻¹ [MOD q]}`.
`y/a` 是自然数除法 (条件 `a·p ≤ y` 的整数解集为 `p ≤ ⌊y/a⌋`). -/
theorem primesInAPBelow_eq_primesInAP_inv (y a q l : ℕ) (ha : 0 < a)
    (hcop : a.Coprime q) :
    primesInAPBelow y a q l = primesInAP (y / a) q (natInvMod q a * l % q) := by
  unfold primesInAPBelow primesInAP
  have hcongr := natInvMod_congr (q := q) (a := a) hcop
  have hiff : (fun p : ℕ => a * p ≡ l [MOD q]) =
      (fun p : ℕ => p ≡ natInvMod q a * l % q [MOD q]) := by
    funext p
    have h1 : (a * p ≡ l [MOD q]) ↔ (p ≡ natInvMod q a * l [MOD q]) :=
      modEq_mul_left_inv_iff hcongr
    have hmod : (p ≡ natInvMod q a * l % q [MOD q]) ↔
        (p ≡ natInvMod q a * l [MOD q]) := by
      have hmm : natInvMod q a * l % q ≡ natInvMod q a * l [MOD q] :=
        (Nat.mod_modEq (a := natInvMod q a * l) (n := q))
      constructor
      · intro hp
        exact hp.trans hmm
      · intro hp
        exact hp.trans hmm.symm
    exact propext (h1.trans hmod.symm)
  have hfilt : (Finset.range (y + 1)).filter
        (fun p => p.Prime ∧ a * p ≤ y ∧ a * p ≡ l [MOD q]) =
      (Finset.range (y / a + 1)).filter
        (fun p => p.Prime ∧ p ≡ natInvMod q a * l % q [MOD q]) := by
    ext p
    constructor
    · intro hp
      rw [Finset.mem_filter] at hp ⊢
      rcases hp with ⟨hpR, hpp, hle, hcong⟩
      constructor
      · rw [Finset.mem_range]
        have hle' : p ≤ y / a :=
          (Nat.le_div_iff_mul_le ha).2 (by simpa [Nat.mul_comm] using hle)
        exact Nat.lt_succ_of_le hle'
      · exact ⟨hpp, (congrFun hiff p).mp hcong⟩
    · intro hp
      rw [Finset.mem_filter] at hp ⊢
      rcases hp with ⟨hpR, hpp, hcong⟩
      have hp_le : p ≤ y / a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hpR)
      have hle : a * p ≤ y := by
        have hle' : p * a ≤ y := (Nat.le_div_iff_mul_le ha).1 hp_le
        simpa [Nat.mul_comm] using hle'
      constructor
      · rw [Finset.mem_range]
        have hp_le_y : p ≤ y := le_trans (Nat.le_mul_of_pos_left p ha) hle
        exact Nat.lt_succ_of_le hp_le_y
      · exact ⟨hpp, ⟨hle, (congrFun hiff p).mpr hcong⟩⟩
  exact congrArg Finset.card hfilt

/-- **a-吸收的分布误差形式** (Liu §II): 对 `(a,q) = 1, a ≥ 1`,

  `Δ(y; a, q, l) = π(y/a; q, l·a⁻¹) − li(y/a)/φ(q)`,

其中 `li` 用真实参数 `(y : ℝ)/a` (实数除法), 与 `π(y/a; ...)` 的整数
截断参数 `y/a` (自然数除法) 区分 — 这是主项 `li(y/a)` 在最终装配时被
显式吸收进筛主项的精确形状. -/
theorem panDistributionError_scaled_inv (y a q l : ℕ) (ha : 0 < a)
    (hcop : a.Coprime q) :
    panDistributionError y a q l =
      ((primesInAP (y / a) q (natInvMod q a * l % q) : ℝ) -
        logarithmicIntegral ((y : ℝ) / a) / Nat.totient q) := by
  unfold panDistributionError
  rw [primesInAPBelow_eq_primesInAP_inv y a q l ha hcop]

/-- **加权分布误差的 Liu §II 形式**: 对任意 `f`, 互素缩放和展开为

  `Σ_{(a,q)=1, a ≤ X} f(a)·Δ(y; a, q, l)
     = Σ_{1 ≤ a ≤ X} [a.Coprime q] · f(a) ·
         (π(y/a; q, l·a⁻¹) − li(y/a)/φ(q)) + (a = 0 项)`.

`a = 0` 项仅在 `q = 1` 时非零 (`0.Coprime q` 当且仅当 `q = 1`), 保留为
未归约项: 经典陈述中 `a` 从 1 开始, 此处显式分离以保持精确性. -/
theorem panDistributionSum_eq_weighted (y X q l : ℕ) (f : ℕ → ℝ) :
    panDistributionSum y X q l f =
      (if (0 : ℕ).Coprime q then f 0 * panDistributionError y 0 q l else 0) +
        ∑ a ∈ Finset.Icc 1 X,
          if a.Coprime q then
            f a * ((primesInAP (y / a) q (natInvMod q a * l % q) : ℝ) -
              logarithmicIntegral ((y : ℝ) / a) / Nat.totient q)
          else 0 := by
  unfold panDistributionSum
  have hrange : Finset.range (X + 1) = insert 0 (Finset.Icc 1 X) := by
    ext a
    constructor
    · intro ha
      rw [Finset.mem_insert]
      by_cases ha0 : a = 0
      · exact Or.inl ha0
      · have hpos : 0 < a := Nat.pos_of_ne_zero ha0
        have haX : a ≤ X := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        exact Or.inr (Finset.mem_Icc.mpr ⟨hpos, haX⟩)
    · intro ha
      rw [Finset.mem_insert] at ha
      rcases ha with rfl | haIcc
      · simp
      · have hmem := Finset.mem_Icc.mp haIcc
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le hmem.2
  rw [hrange, Finset.sum_insert (by simp)]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hcop : a.Coprime q
  · rw [if_pos hcop, if_pos hcop]
    congr 1
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    exact panDistributionError_scaled_inv y a q l (by omega) hcop
  · simp [hcop]

/-! ## 3. max 脚手架: `panMaxL`/`panMaxY` 的去 max 界 -/

/-- 每个 `|panDistributionSum|` 非负, 故 `panMaxL` (有限集 max, 空集取 0)
非负. -/
theorem panMaxL_nonneg (y X q : ℕ) (f : ℕ → ℝ) : 0 ≤ panMaxL y X q f := by
  unfold panMaxL
  by_cases h : ((Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q)).Nonempty
  · dsimp only []
    rw [dif_pos h]
    rcases h with ⟨l, hl⟩
    have hl' : |panDistributionSum y X q l f| ∈
        (Finset.image (fun l : ℕ => |panDistributionSum y X q l f|)
          ((Finset.Icc 1 (q - 1)).filter (fun l : ℕ => l.Coprime q))) := by
      exact Finset.mem_image.mpr ⟨l, hl, rfl⟩
    exact le_trans (abs_nonneg _) (Finset.le_max' _ _ hl')
  · dsimp only []
    rw [dif_neg h]

/-- `panMaxL` 被剩余类上的绝对值和对控制: `max_{l} |·| ≤ Σ_{l} |·|`. -/
theorem panMaxL_le_sum_abs (y X q : ℕ) (f : ℕ → ℝ)
    (hS : ((Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q)).Nonempty) :
    panMaxL y X q f ≤
      ∑ l ∈ (Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q),
        |panDistributionSum y X q l f| := by
  unfold panMaxL
  dsimp only []
  rw [dif_pos hS]
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨l, hl, rfl⟩
  exact Finset.single_le_sum (fun l' hl' => abs_nonneg (panDistributionSum y X q l' f)) hl

/-- `panMaxY` (对 `y` 的 max) 被逐 `y` 的 `panMaxL` 和所控制. -/
theorem panMaxY_le_sum (X q x : ℕ) (f : ℕ → ℝ) :
    panMaxY X q x f ≤ ∑ y ∈ Finset.range (x + 1), panMaxL y X q f := by
  unfold panMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  exact Finset.single_le_sum (fun y' hy' => panMaxL_nonneg y' X q f) hy

/-- 组合: `panMaxY ≤ Σ_{y ≤ x} Σ_{(l,q)=1} |panDistributionSum y X q l f|`
(装配期把双 max 换成有限和, 供 type I/type II 逐项估计). -/
theorem panMaxY_le_sum_abs (X q x : ℕ) (f : ℕ → ℝ)
    (hS : ((Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q)).Nonempty) :
    panMaxY X q x f ≤
      ∑ y ∈ Finset.range (x + 1),
        ∑ l ∈ (Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q),
          |panDistributionSum y X q l f| := by
  exact le_trans (panMaxY_le_sum X q x f)
    (Finset.sum_le_sum (fun y hy => panMaxL_le_sum_abs y X q f hS))


/-! ## 4. 开放引理: type I / type II / 主项 台阶 (经典解析输入, 精确陈述)

经典证明 (Liu 2022 §III; Halberstam--Richert 1974 Ch.10) 在 a-吸收 (Section 2)
之后, 对每个 `(y, a, q, l)` 把 a-吸收误差拆成 **type I** (Vaughan V1, 小因子
`d ≤ u`), **type II** (Vaughan V3, 双线性 `d > u, e > v`) 与 **主项**
(`li` 和 `apV2` 中项) 三块, 逐块估计后装配. 下列 `def ... : Prop` 是
三块估计的精确陈述 (研究目标, 与 `PanMeanValueUniform` 同等级; 证明依赖
Farey 点大筛 `LargeSieve.Multiplicative.largeSieveRationalPoints`,
模 q 特征大筛 `characterSieveModulus_le`, Vaughan 恒等式
`Sieve.VaughanIdentity`, 与 PNT 主项 `PrimeDistribution`). 不引入公理,
不 sorry; 落地后替换为 theorem 并移除本条注释的 "OPEN" 标记.
-/

/-- a-吸收后的等差 von Mangoldt 计数: `Σ_{n ≤ y, n ≡ l [MOD q]} Λ(n)`
(`ψ` 的等差版本). Vaughan 三段分解 (`vaughanIdentity`) 逐项作用在
`Λ n` 上, 给出 type I / type II 片段 (下述 `apV1`/`apV3`) 的定义基底. -/
noncomputable def apVonMangoldt (y q l : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), if n ≡ l [MOD q] then Λ n else 0

/-- **type I 片段** (Vaughan V1): `Σ_{n ≤ y, n ≡ l [MOD q]} Σ_{d | n, d ≤ u} μ(d)·log(n/d)`. -/
noncomputable def apV1 (y q l u : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), if n ≡ l [MOD q] then vaughanFirst n u else 0

/-- **type II 片段** (Vaughan V3): `Σ_{n ≤ y, n ≡ l [MOD q]} Σ_{d | n, u < d} Σ_{e | n/d, v < e} μ(d)·Λ(e)`. -/
noncomputable def apV3 (y q l u v : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), if n ≡ l [MOD q] then vaughanThird n u v else 0

/-- 片段加权和 (去 max 前的对象): `Σ_{1 ≤ a ≤ X, (a,q)=1} f(a)·g(y/a, q, l·a⁻¹ mod q)`,
即 a-吸收 (Section 2) 后对任意片段函数 `g` 的加权和 (a = 0 项分离在
`panDistributionSum_eq_weighted` 中, 此处只取 `1 ≤ a`). -/
noncomputable def panPieceSum (y X q l : ℕ) (f : ℕ → ℝ) (g : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X, if a.Coprime q then f a * g (y / a) q (natInvMod q a * l % q) else 0

/-- 片段加权和的 `l`-max: 镜像 `panMaxL`. -/
noncomputable def panPieceMaxL (y X q : ℕ) (f : ℕ → ℝ) (g : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  let S : Finset ℕ := (Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q)
  if h : S.Nonempty then
    (S.image (fun l => |panPieceSum y X q l f g|)).max' (Finset.image_nonempty.mpr h)
  else 0

/-- 片段加权和的 `y`-max 包装: 镜像 `panMaxY`. -/
noncomputable def panPieceMaxY (X q x : ℕ) (f : ℕ → ℝ) (g : ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ((Finset.range (x + 1)).image (fun y => panPieceMaxL y X q f g)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- **开放引理 T1 (加权 type I 界)**: 对每个 `A > 0` 存在 `C, B, x₀` 使得
对所有 `X ≥ x₀`, `Q := (xX)^{1/2}/log^B(xX)`,

  `Σ_{q ≤ Q} μ²(q)·3^{ω(q)}·max_{y ≤ xX} max_{(l,q)=1}
     |Σ_{(a,q)=1, a ≤ X} f(a)·apV1(y/a; q, l·a⁻¹; u)/log(y/a)|
     ≤ C·xX/log^A(xX)`.

对 `|f| ≤ 1` 一致成立 (经典证明: 小因子部分 `d ≤ u` 用大筛在 Farey 点
的均值定理 + 特征展开; Liu §III Lemma 1; HR 1974 Ch.10). -/
def PanTypeIWeightedBound (x f : ℕ → ℝ) (u : ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
    ∀ X : ℕ, x₀ ≤ X →
      ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panPieceMaxY X q (Nat.floor (x X)) f
            (fun y q l => apV1 y q l u / Real.log (y : ℝ)) ≤
        C * x X / (log (x X)) ^ A

/-- **开放引理 T2 (加权 type II 界)**: 双线性片段 (Vaughan V3) 的加权均值界,
对 `|α|, |β| ≤ 1` 一致; 经典证明用大筛均值定理 (Farey 点
`largeSieveRationalPoints`) 控制 `Σ_{q ≤ Q} Σ_{(l,q)=1} |Σ α(d)β(e)·e(de·l/q)|²`
再经 Cauchy--Schwarz 装配 (Liu §III; Montgomery 均值定理). -/
def PanTypeIIWeightedBound (x f : ℕ → ℝ) (u v : ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
    ∀ X : ℕ, x₀ ≤ X →
      ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panPieceMaxY X q (Nat.floor (x X)) f
            (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) ≤
        C * x X / (log (x X)) ^ A

/-- **开放引理 T3 (主项界)**: `li` 主项部分的加权和 (`Σ_{(a,q)=1} f(a)·li(y/a)/φ(q)`)
在装配中被筛主项吸收后余下的界; 依赖 PNT 级主项估计
(`PrimeDistribution.primeCounting_asymptotic_real` 等) 与
`li(x) = x/log x + O(x/log²x)` (Liu §III; ROADMAP BRG 节点). -/
def PanMainTermBound (x f : ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
    ∀ X : ℕ, x₀ ≤ X →
      ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panPieceMaxY X q (Nat.floor (x X)) f
            (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q) ≤
        C * x X / (log (x X)) ^ A


/-! ## 5. T1: type I 加权界的有限代数归约 (character-mean-value 归约)

经典证明 (Liu 2022 §III Lemma 1; HR 1974 Ch.10) 中 type I 片段 (Vaughan V1, 小因子
d ≤ u 部分) 的加权界被本节的有限代数链精确归约到一个特征均值对象:

```text
apV1 的等差和 --[charSum_ap 特征展开]--> 特征和 V_chi(y,u) = Σ_{n<=y} vaughanFirst(n,u)*chi(n)
  --[点式界 |apV1| <= phi(q)^-1 * Σ_chi ||V_chi|| (|chi(l)| = 1)]--> 单项三角形归约
  --[l-一致界 (与 l 无关)]--> panPieceMaxL <= panTypeIDistributionSum
  --[y-max 归约]--> panPieceMaxY <= panTypeIMeanValueMaxY
  --[权重单调]--> PanTypeICharacterMeanValue => PanTypeIWeightedBound
```

唯一的剩余解析输入是 PanTypeICharacterMeanValue (特征均值界, 经典证明用乘法
大筛对 Σ_chi||V_chi||^2 的均值 + Cauchy-Schwarz 装配), 见 §4 开放引理表的 T1 条目.
-/
noncomputable section

set_option linter.style.haveILetI false

/-- 单位剩余类代表集 {1 ≤ l ≤ q-1 : (l,q) = 1} (q ≤ 1 时为空集). -/
noncomputable def unitResidues (q : ℕ) : Finset ℕ := (Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q)

/-- type I 片段的特征和: V_χ(y,u) = Σ_{n ≤ y} vaughanFirst(n,u)·χ(n) (复值). -/
noncomputable def panTypeIV1CharSum (q y u : ℕ) (χ : DirichletCharacter ℂ q) : ℂ := 
  ∑ n ∈ Finset.range (y + 1), (vaughanFirst n u : ℂ) * χ (n : ZMod q)

/-- 单位上 Dirichlet 特征值的模为 1: χ(l) 是单位群元素 (有限阶) 的像, 是单位根. -/
theorem charValue_norm_eq_one {q : ℕ} {χ : DirichletCharacter ℂ q} {l : ℕ}
    (hl : IsUnit (l : ZMod q)) : ‖χ (l : ZMod q)‖ = 1 := by
  haveI : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  let n : ℕ := Fintype.card (ZMod q)ˣ
  have hn : n ≠ 0 := by
    exact ne_of_gt (Fintype.card_pos (α := (ZMod q)ˣ))
  have hpow_u : hl.unit ^ n = 1 := pow_card_eq_one (G := (ZMod q)ˣ) (x := hl.unit)
  have hpow_l : (l : ZMod q) ^ n = 1 := by
    have hspec : (l : ZMod q) = (hl.unit : ZMod q) := hl.unit_spec.symm
    rw [hspec]
    simpa using congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) hpow_u
  have hpow_χ : (χ (l : ZMod q)) ^ n = 1 := by
    rw [← map_pow, hpow_l, map_one]
  exact Complex.norm_eq_one_of_pow_eq_one hpow_χ hn

/-- apV1 的特征展开 (复值): (apV1 y q l u : ℂ) = φ(q)⁻¹·Σ_χ star(χ(l))·V_χ(y,u)
    (对单位 l; 由 charSum_ap 直接给出). -/
theorem apV1_charSum {q y u : ℕ} (hq : 0 < q) {l : ℕ} (hl : IsUnit (l : ZMod q)) :
    (apV1 y q l u : ℂ) = (Nat.totient q : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, star (χ (l : ZMod q)) * panTypeIV1CharSum q y u χ := by
  unfold apV1 panTypeIV1CharSum
  have hcast : ((∑ n ∈ Finset.range (y + 1),
        (if n ≡ l [MOD q] then vaughanFirst n u else 0) : ℝ) : ℂ) =
      ∑ n ∈ Finset.range (y + 1),
        (vaughanFirst n u : ℂ) * (if n ≡ l [MOD q] then 1 else 0) := by
    calc
      ((∑ n ∈ Finset.range (y + 1),
          (if n ≡ l [MOD q] then vaughanFirst n u else 0) : ℝ) : ℂ)
          = ∑ n ∈ Finset.range (y + 1),
              ((if n ≡ l [MOD q] then vaughanFirst n u else 0 : ℝ) : ℂ) := by
            exact map_sum Complex.ofRealHom
              (fun n => (if n ≡ l [MOD q] then vaughanFirst n u else 0 : ℝ)) (Finset.range (y + 1))
      _ = ∑ n ∈ Finset.range (y + 1),
            (vaughanFirst n u : ℂ) * (if n ≡ l [MOD q] then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro n hn
          by_cases hmod : n ≡ l [MOD q] <;> simp [hmod]
  rw [hcast]
  exact AnalyticNumberTheory.LargeSieve.charSum_ap hq hl (fun n : ℕ => (vaughanFirst n u : ℂ)) y

/-- apV1 点式界: 对单位 l, |apV1 y q l u| ≤ φ(q)⁻¹·Σ_χ ‖V_χ(y,u)‖. -/
theorem apV1_abs_le {q y u : ℕ} (hq : 0 < q) {l : ℕ} (hl : IsUnit (l : ZMod q)) :
    |apV1 y q l u| ≤ (Nat.totient q : ℝ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q y u χ‖ := by
  have hnorm : ‖(apV1 y q l u : ℂ)‖ = |apV1 y q l u| := by
    exact RCLike.norm_ofReal (apV1 y q l u)
  rw [← hnorm]
  rw [apV1_charSum hq hl]
  calc
    ‖(Nat.totient q : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        star (χ (l : ZMod q)) * panTypeIV1CharSum q y u χ‖
        ≤ ‖(Nat.totient q : ℂ)⁻¹‖ * ‖∑ χ : DirichletCharacter ℂ q,
            star (χ (l : ZMod q)) * panTypeIV1CharSum q y u χ‖ := by
          exact norm_mul_le _ _
    _ = (Nat.totient q : ℝ)⁻¹ * ‖∑ χ : DirichletCharacter ℂ q,
            star (χ (l : ZMod q)) * panTypeIV1CharSum q y u χ‖ := by
          congr 1
          rw [norm_inv, Complex.norm_natCast]
    _ ≤ (Nat.totient q : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          ‖star (χ (l : ZMod q)) * panTypeIV1CharSum q y u χ‖ := by
          exact mul_le_mul_of_nonneg_left (norm_sum_le _ _)
            (inv_nonneg.mpr (Nat.cast_nonneg (Nat.totient q)))
    _ ≤ (Nat.totient q : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          ‖panTypeIV1CharSum q y u χ‖ := by
          exact mul_le_mul_of_nonneg_left
            (by
              apply Finset.sum_le_sum
              intro χ hχ
              calc
                ‖star (χ (l : ZMod q)) * panTypeIV1CharSum q y u χ‖
                    ≤ ‖star (χ (l : ZMod q))‖ * ‖panTypeIV1CharSum q y u χ‖ := norm_mul_le _ _
                _ = ‖χ (l : ZMod q)‖ * ‖panTypeIV1CharSum q y u χ‖ := by
                      congr 1
                      simpa using (Complex.norm_conj (χ (l : ZMod q)))
                _ = ‖panTypeIV1CharSum q y u χ‖ := by
                      rw [charValue_norm_eq_one hl]
                      simp)
            (inv_nonneg.mpr (Nat.cast_nonneg (Nat.totient q)))

/-- 模 q 单位 a 的逆代表与单位 l 的乘积剩余类仍是单位 (用于 apV1 点式界). -/
lemma isUnit_natInvMod_mul_residue {q a l : ℕ} (hq : 0 < q) (hcop_a : a.Coprime q)
    (hl : l.Coprime q) : IsUnit (((natInvMod q a * l % q) : ℕ) : ZMod q) := by
  haveI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hval : (((natInvMod q a * l % q : ℕ) : ZMod q)) =
      (((natInvMod q a * l : ℕ) : ZMod q)) := by
    have hz := ZMod.natCast_zmod_val (((natInvMod q a * l : ℕ) : ZMod q))
    simpa [ZMod.val_natCast] using hz
  rw [hval, Nat.cast_mul]
  have hni : (natInvMod q a : ZMod q) = (a⁻¹ : ZMod q) := by
    unfold natInvMod
    rw [dif_pos hcop_a]
    exact ZMod.natCast_zmod_val (a⁻¹ : ZMod q)
  have hui : IsUnit (a⁻¹ : ZMod q) := by
    refine ⟨⟨(a⁻¹ : ZMod q), (a : ZMod q), ?_, ?_⟩, rfl⟩
    · rw [mul_comm]
      exact ZMod.coe_mul_inv_eq_one a hcop_a
    · exact ZMod.coe_mul_inv_eq_one a hcop_a
  have hni_unit : IsUnit (natInvMod q a : ZMod q) := by
    rw [hni]
    exact hui
  have hl' : IsUnit (l : ZMod q) := (ZMod.isUnit_iff_coprime l q).mpr hl
  refine ⟨hni_unit.unit * hl'.unit, ?_⟩
  simp [Units.val_mul]

/-- **type I 的分布和 (开放引理的对象)**: 对每个 y, 把 a-吸收后的 type I 片段
  加权和归约到的特征均值对象:
  Σ_{a ≤ X} |f(a)|/|log(y/a)| · Σ_χ ‖V_χ(y/a, u)‖. -/
noncomputable def panTypeIDistributionSum (y X q : ℕ) (f : ℕ → ℝ) (u : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X,
    |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
      ∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖

/-- 分布和非负. -/
theorem panTypeIDistributionSum_nonneg (y X q : ℕ) (f : ℕ → ℝ) (u : ℕ) :
    0 ≤ panTypeIDistributionSum y X q f u := by
  unfold panTypeIDistributionSum
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _))
    (Finset.sum_nonneg (fun χ hχ => norm_nonneg _))

/-- type I 单项的三角形归约: 对互素 a 与单位 l,
  |f(a)·apV1(y/a; q, a⁻¹l)/log(y/a)| ≤ |f(a)|/|log(y/a)| · Σ_χ ‖V_χ(y/a, u)‖
  (特征展开点式界 + φ(q)⁻¹ ≤ 1). -/
private lemma panTypeI_summand_abs_le (y _X q : ℕ) (f : ℕ → ℝ) (u a l : ℕ)
    (hq : 0 < q) (hcop : a.Coprime q) (hl : l.Coprime q) :
    |f a * (apV1 (y / a) q (natInvMod q a * l % q) u / Real.log ((y / a : ℕ) : ℝ))|
      ≤ |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          ∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖ := by
  calc
    |f a * (apV1 (y / a) q (natInvMod q a * l % q) u / Real.log ((y / a : ℕ) : ℝ))|
        = |f a| * |apV1 (y / a) q (natInvMod q a * l % q) u / Real.log ((y / a : ℕ) : ℝ)| := by
          rw [abs_mul]
    _ = |f a| * (|apV1 (y / a) q (natInvMod q a * l % q) u| / |Real.log ((y / a : ℕ) : ℝ)|) := by
          rw [abs_div]
    _ ≤ |f a| * (((Nat.totient q : ℝ)⁻¹ *
            ∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖) /
            |Real.log ((y / a : ℕ) : ℝ)|) := by
          have h1 : |apV1 (y / a) q (natInvMod q a * l % q) u| ≤
              (Nat.totient q : ℝ)⁻¹ *
                ∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖ :=
            apV1_abs_le (q := q) (y := y / a) (u := u) hq (isUnit_natInvMod_mul_residue hq hcop hl)
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 (abs_nonneg _)) (abs_nonneg _)
    _ = |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          ((Nat.totient q : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖) := by
          ring
    _ ≤ |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖) := by
          have hqpos : 0 < (Nat.totient q : ℝ) := by
            exact_mod_cast (Nat.totient_pos.mpr hq)
          have hq1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
            exact_mod_cast (Nat.succ_le_of_lt (Nat.totient_pos.mpr hq))
          have hφ : (Nat.totient q : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hqpos).mpr hq1
          have hS : 0 ≤ (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖) := by
            apply Finset.sum_nonneg
            intro χ hχ
            exact norm_nonneg _
          have hPhiS : (Nat.totient q : ℝ)⁻¹ * (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖) ≤
              (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖) := by
            simpa using (mul_le_mul_of_nonneg_right hφ hS)
          exact mul_le_mul_of_nonneg_left hPhiS
            (div_nonneg (abs_nonneg _) (abs_nonneg _))

/-- **type I 的 l-一致归约**: 对单位 l, 每个 |panPieceSum y X q l f g| 被
  panTypeIDistributionSum 一致控制 (界与 l 无关). -/
theorem panPieceSum_typeI_abs_le (y X q : ℕ) (f : ℕ → ℝ) (u l : ℕ) (hq : 0 < q)
    (hl : l.Coprime q) :
    |panPieceSum y X q l f (fun y' q' l' => apV1 y' q' l' u / Real.log (y' : ℝ))|
      ≤ panTypeIDistributionSum y X q f u := by
  calc
    |panPieceSum y X q l f (fun y' q' l' => apV1 y' q' l' u / Real.log (y' : ℝ))|
        ≤ ∑ a ∈ Finset.Icc 1 X,
            |if a.Coprime q then
              f a * (apV1 (y / a) q (natInvMod q a * l % q) u / Real.log ((y / a : ℕ) : ℝ))
            else 0| := by
          unfold panPieceSum
          exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.Icc 1 X,
          |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
            ∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖ := by
          apply Finset.sum_le_sum
          intro a ha
          by_cases hcop : a.Coprime q
          · rw [if_pos hcop]
            exact panTypeI_summand_abs_le y X q f u a l hq hcop hl
          · have hnonneg : 0 ≤ |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
                ∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖ := by
              exact mul_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _))
                (Finset.sum_nonneg (fun χ hχ => norm_nonneg _))
            simp [hcop]
            exact hnonneg

/-- **l-max 归约**: panPieceMaxL ≤ panTypeIDistributionSum (界与 l 无关, 故 max 直接进入). -/
theorem panPieceMaxL_le_typeIDistributionSum (y X q : ℕ) (f : ℕ → ℝ) (u : ℕ) :
    panPieceMaxL y X q f (fun y' q' l' => apV1 y' q' l' u / Real.log (y' : ℝ)) ≤
      panTypeIDistributionSum y X q f u := by
  unfold panPieceMaxL
  by_cases hS : ((Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q)).Nonempty
  · dsimp only []
    rw [dif_pos hS]
    apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨l, hl, rfl⟩
    have hlS : l ∈ (Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q) := hl
    have hl' : l.Coprime q := (Finset.mem_filter.mp hlS).2
    have hlIcc : l ∈ Finset.Icc 1 (q - 1) := (Finset.mem_filter.mp hlS).1
    have hq : 0 < q := by
      have h1 : 1 ≤ l := (Finset.mem_Icc.mp hlIcc).1
      have h2 : l ≤ q - 1 := (Finset.mem_Icc.mp hlIcc).2
      omega
    exact panPieceSum_typeI_abs_le y X q f u l hq hl'
  · rw [dif_neg hS]
    exact panTypeIDistributionSum_nonneg y X q f u

/-- **特征均值对象的 y-max**: 镜像 panPieceMaxY. -/
noncomputable def panTypeIMeanValueMaxY (X q x : ℕ) (f : ℕ → ℝ) (u : ℕ) : ℝ :=
  ((Finset.range (x + 1)).image (fun y => panTypeIDistributionSum y X q f u)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- **y-max 归约**: panPieceMaxY ≤ panTypeIMeanValueMaxY (逐 y 的
  panPieceMaxL ≤ panTypeIDistributionSum 后取 max). -/
theorem panPieceMaxY_le_typeIMeanValueMaxY (X q x : ℕ) (f : ℕ → ℝ) (u : ℕ) :
    panPieceMaxY X q x f (fun y' q' l' => apV1 y' q' l' u / Real.log (y' : ℝ)) ≤
      panTypeIMeanValueMaxY X q x f u := by
  unfold panPieceMaxY panTypeIMeanValueMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  exact le_trans (panPieceMaxL_le_typeIDistributionSum y X q f u)
    (Finset.le_max'
      (s := (Finset.range (x + 1)).image (fun y => panTypeIDistributionSum y X q f u))
      (x := panTypeIDistributionSum y X q f u)
      (Finset.mem_image.mpr ⟨y, hy, rfl⟩))

/-- **开放引理 T1' (特征均值界)**: type I 的剩余分析输入 — 在 3^{ω(q)} 权重下
  特征均值对象的界 (对 |f| ≤ 1 一致; 经典证明: 乘法大筛对 Σ_χ‖V_χ‖² 的均值
  + Cauchy-Schwarz 装配). 这是 PanTypeIWeightedBound 归约后剩下的唯一解析台阶. -/
def PanTypeICharacterMeanValue (x : ℕ → ℝ) (f : ℕ → ℝ) (u : ℕ) : Prop :=
  (∀ a : ℕ, |f a| ≤ 1) ∧
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
      ∀ X : ℕ, x₀ ≤ X →
        ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            panTypeIMeanValueMaxY X q (Nat.floor (x X)) f u ≤
          C * x X / (log (x X)) ^ A

/-- **T1 归约定理**: PanTypeICharacterMeanValue (特征均值, 开放) ⇒
  PanTypeIWeightedBound (加权 type I 界). 全部有限代数 (特征展开, 点式界,
  l-max/y-max 归约, 权重单调) 在此证明; 剩下的唯一解析输入是特征均值界本身. -/
theorem PanTypeIWeightedBound.of_characterMeanValue {x : ℕ → ℝ} {f : ℕ → ℝ} {u : ℕ} :
    PanTypeICharacterMeanValue x f u → PanTypeIWeightedBound x f u := by
  intro hP
  rcases hP with ⟨hfb, hBound⟩
  intro A hA
  rcases hBound A hA with ⟨C, hC, B, x₀, hMain⟩
  refine ⟨C, hC, B, x₀, ?_⟩
  intro X hX
  calc
    (∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panPieceMaxY X q (Nat.floor (x X)) f
            (fun y q l => apV1 y q l u / Real.log (y : ℝ)))
        ≤ ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              panTypeIMeanValueMaxY X q (Nat.floor (x X)) f u := by
          apply Finset.sum_le_sum
          intro q hq
          have hw : 0 ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card := by
            exact mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num) _)
          exact mul_le_mul_of_nonneg_left
            (panPieceMaxY_le_typeIMeanValueMaxY X q (Nat.floor (x X)) f u) hw
    _ ≤ C * x X / (log (x X)) ^ A := hMain X hX

/-! ## 5.1 T1': 特征均值界的归约链 (Cauchy--Schwarz 块 + 乘法大筛均值输入)

经典证明 (Liu 2022 §III Lemma 1; HR 1974 Ch.10) 中 type I 特征均值界的剩余
解析台阶是:

```text
Σ_{q ≤ Q} μ²(q)·3^{ω(q)}·max_{y ≤ xX} Σ_{a ≤ X} |f(a)|/|log(y/a)|·Σ_χ ‖V_χ(y/a)‖
  --[Cauchy--Schwarz, 特征个数 = φ(q)]-->
  Σ_{q ≤ Q} μ²(q)·3^{ω(q)}·φ(q)^{1/2}·max_{y ≤ xX} Σ_{a ≤ X} |f(a)|/|log(y/a)|·(Σ_χ ‖V_χ(y/a)‖²)^{1/2}
  --[乘法大筛均值 (Bombieri--Davenport) + vaughanFirst 平方和 + 权重 φ-和 + 外层 (y,a) 权重和]-->
  C·xX/log^A(xX)
```

本小节落地**全部有限代数**: Cauchy--Schwarz 块 (`panTypeI_charAbsSum_le_cs`,
特征个数 = φ(q), `DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity`),
逐 a 加权 CS (`panTypeIDistributionSum_le_csWeighted`), y-max 归约
(`panTypeIMeanValueMaxY_le_charSqrtMeanMaxY`), 权重单调
(`panTypeI_weight_nonneg`), |f| ≤ 1 简化
(`panTypeICharSqrtMeanMaxY_le_of_abs_le_one`), 以及最终归约定理
`PanTypeICharacterMeanValue.of_sieveBound` (零 sorry).

乘法大筛均值本身 (求和到 `q ≤ Q` 的**全体**特征版本) 需要原特征分解与 Gauss 和
(见 `Multiplicative.lean` 模块头红队注记), 降级为辅助 Prop
`panTypeICharMeanSieveBound` (经典 Bombieri--Davenport 装配形式), 另附文档化
核心 `panTypeICharSquareMeanBound`. 红队注记: 直接对全体特征叠加 Parseval
路线不成立 (反例: `a_n ≡ 1`, `Q = 2`, `N` 充分大: 左边
`Σ_q (q/φ(q))Σ_χ|S(χ)|² ≈ 3N²/2` 而 `C(N,1/4)·N = (N+64)·N`).
-/

/-- 特征和的 L² 对象: t_q(m) = Σ_χ ‖V_χ(m)‖² (乘法大筛均值的自然对象). -/
noncomputable def panTypeICharSqSum (q m u : ℕ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q m u χ‖ ^ 2

/-- **Cauchy--Schwarz 块**: Σ_χ ‖V_χ(m)‖ ≤ φ(q)^{1/2}·(Σ_χ ‖V_χ(m)‖²)^{1/2},
  由特征个数 = φ(q) 与标准 `(Σa_i)² ≤ n·Σa_i²` 给出. -/
theorem panTypeI_charAbsSum_le_cs (q m u : ℕ) (hq : 0 < q) :
    (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q m u χ‖) ≤
      Real.sqrt (Nat.totient q : ℝ) * Real.sqrt (panTypeICharSqSum q m u) := by
  haveI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ) :=
    AnalyticNumberTheory.LargeSieve.complexHasEnoughRootsOfUnity (Monoid.exponent (ZMod q)ˣ)
      (Monoid.exponent_ne_zero_of_finite (G := (ZMod q)ˣ))
  have hcard : Fintype.card (DirichletCharacter ℂ q) = Nat.totient q := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hcs : (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q m u χ‖) ^ 2 ≤
      (Nat.totient q : ℝ) * panTypeICharSqSum q m u := by
    calc
      (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q m u χ‖) ^ 2
          ≤ (Fintype.card (DirichletCharacter ℂ q) : ℝ) *
              (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q m u χ‖ ^ 2) := by
            simpa using (sq_sum_le_card_mul_sum_sq
              (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
              (f := fun χ : DirichletCharacter ℂ q => ‖panTypeIV1CharSum q m u χ‖))
      _ = (Nat.totient q : ℝ) * panTypeICharSqSum q m u := by
            rw [hcard, panTypeICharSqSum]
  have hS : 0 ≤ panTypeICharSqSum q m u := by
    unfold panTypeICharSqSum
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hφ : 0 ≤ (Nat.totient q : ℝ) := by positivity
  have hsq : (∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q m u χ‖) ^ 2 ≤
      (Real.sqrt (Nat.totient q : ℝ) * Real.sqrt (panTypeICharSqSum q m u)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hφ, Real.sq_sqrt hS]
    exact hcs
  exact le_of_sq_le_sq hsq (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- 分布和的逐 a 加权 CS 归约:
  panTypeIDistributionSum y X q f u ≤ φ(q)^{1/2}·Σ_{a ≤ X} |f(a)|/|log(y/a)|·t_q(y/a)^{1/2}. -/
theorem panTypeIDistributionSum_le_csWeighted (y X q : ℕ) (f : ℕ → ℝ) (u : ℕ) (hq : 0 < q) :
    panTypeIDistributionSum y X q f u ≤
      Real.sqrt (Nat.totient q : ℝ) *
        (∑ a ∈ Finset.Icc 1 X,
          |f a| / |Real.log ((y / a : ℕ) : ℝ)| * Real.sqrt (panTypeICharSqSum q (y / a) u)) := by
  unfold panTypeIDistributionSum
  calc
    (∑ a ∈ Finset.Icc 1 X,
        |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          ∑ χ : DirichletCharacter ℂ q, ‖panTypeIV1CharSum q (y / a) u χ‖)
        ≤ ∑ a ∈ Finset.Icc 1 X,
            |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
              (Real.sqrt (Nat.totient q : ℝ) * Real.sqrt (panTypeICharSqSum q (y / a) u)) := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (panTypeI_charAbsSum_le_cs q (y / a) u hq)
            (div_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = Real.sqrt (Nat.totient q : ℝ) *
          (∑ a ∈ Finset.Icc 1 X,
            |f a| / |Real.log ((y / a : ℕ) : ℝ)| * Real.sqrt (panTypeICharSqSum q (y / a) u)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          ring

/-- 特征平方和加权对象的逐 y 切片 (乘法大筛均值输入的 y 分量):
  W(y) = Σ_{a ≤ X} |f(a)|/|log(y/a)|·t_q(y/a)^{1/2}. -/
noncomputable def panTypeICharSqrtMean (y X q : ℕ) (f : ℕ → ℝ) (u : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X,
    |f a| / |Real.log ((y / a : ℕ) : ℝ)| * Real.sqrt (panTypeICharSqSum q (y / a) u)

/-- 特征平方和加权对象的 y-max (乘法大筛均值输入): 镜像 panTypeIMeanValueMaxY. -/
noncomputable def panTypeICharSqrtMeanMaxY (X q x : ℕ) (f : ℕ → ℝ) (u : ℕ) : ℝ :=
  ((Finset.range (x + 1)).image (fun y => panTypeICharSqrtMean y X q f u)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- **y-max 归约**: panTypeIMeanValueMaxY ≤ φ(q)^{1/2}·panTypeICharSqrtMeanMaxY
  (逐 y 的加权 CS 后取 max). -/
theorem panTypeIMeanValueMaxY_le_charSqrtMeanMaxY (X q x : ℕ) (f : ℕ → ℝ) (u : ℕ) (hq : 0 < q) :
    panTypeIMeanValueMaxY X q x f u ≤
      Real.sqrt (Nat.totient q : ℝ) * panTypeICharSqrtMeanMaxY X q x f u := by
  unfold panTypeIMeanValueMaxY panTypeICharSqrtMeanMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  calc
    panTypeIDistributionSum y X q f u
        ≤ Real.sqrt (Nat.totient q : ℝ) * panTypeICharSqrtMean y X q f u :=
          panTypeIDistributionSum_le_csWeighted y X q f u hq
    _ ≤ Real.sqrt (Nat.totient q : ℝ) * panTypeICharSqrtMeanMaxY X q x f u := by
          exact mul_le_mul_of_nonneg_left
            (Finset.le_max'
              (s := (Finset.range (x + 1)).image (fun y => panTypeICharSqrtMean y X q f u))
              (x := panTypeICharSqrtMean y X q f u)
              (Finset.mem_image.mpr ⟨y, hy, rfl⟩))
            (Real.sqrt_nonneg _)

/-- 权重非负: μ²(q)·3^{ω(q)} ≥ 0. -/
theorem panTypeI_weight_nonneg (q : ℕ) :
    0 ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card := by
  exact mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num) _)

/-- 带权重的逐 q 归约: w_q·M_q ≤ w_q·φ(q)^{1/2}·W_q (q = 0 时权重为 0, 平凡). -/
private lemma panTypeI_weighted_maxY_le_weighted_sqrtMean (X q x : ℕ) (f : ℕ → ℝ) (u : ℕ) :
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * panTypeIMeanValueMaxY X q x f u ≤
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
        Real.sqrt (Nat.totient q : ℝ) * panTypeICharSqrtMeanMaxY X q x f u := by
  by_cases hq0 : q = 0
  · subst q
    have hμ : (μ 0 : ℤ) = 0 := by
      exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree (not_squarefree_zero)
    simp [hμ, Nat.totient_zero]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    calc
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * panTypeIMeanValueMaxY X q x f u
          ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              (Real.sqrt (Nat.totient q : ℝ) * panTypeICharSqrtMeanMaxY X q x f u) := by
            exact mul_le_mul_of_nonneg_left
              (panTypeIMeanValueMaxY_le_charSqrtMeanMaxY X q x f u hq)
              (panTypeI_weight_nonneg q)
      _ = ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            Real.sqrt (Nat.totient q : ℝ) * panTypeICharSqrtMeanMaxY X q x f u := by
            ring

/-- **|f| ≤ 1 简化**: |f(a)| ≤ 1 时, 特征平方和加权对象的 y-max 被
  f ≡ 1 的版本一致控制. -/
theorem panTypeICharSqrtMeanMaxY_le_of_abs_le_one (X q x : ℕ) (u : ℕ) {f : ℕ → ℝ}
    (hfb : ∀ a : ℕ, |f a| ≤ 1) :
    panTypeICharSqrtMeanMaxY X q x f u ≤ panTypeICharSqrtMeanMaxY X q x (fun _ : ℕ => 1) u := by
  unfold panTypeICharSqrtMeanMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  calc
    panTypeICharSqrtMean y X q f u
        ≤ panTypeICharSqrtMean y X q (fun _ : ℕ => 1) u := by
          unfold panTypeICharSqrtMean
          apply Finset.sum_le_sum
          intro a ha
          have hdiv : |f a| / |Real.log ((y / a : ℕ) : ℝ)| ≤
              (1 : ℝ) / |Real.log ((y / a : ℕ) : ℝ)| :=
            div_le_div_of_nonneg_right (hfb a) (abs_nonneg _)
          have hsqrt : 0 ≤ Real.sqrt (panTypeICharSqSum q (y / a) u) := Real.sqrt_nonneg _
          calc
            |f a| / |Real.log ((y / a : ℕ) : ℝ)| * Real.sqrt (panTypeICharSqSum q (y / a) u)
                ≤ (1 : ℝ) / |Real.log ((y / a : ℕ) : ℝ)| *
                    Real.sqrt (panTypeICharSqSum q (y / a) u) :=
                  mul_le_mul_of_nonneg_right hdiv hsqrt
            _ = |(1 : ℝ)| / |Real.log ((y / a : ℕ) : ℝ)| *
                  Real.sqrt (panTypeICharSqSum q (y / a) u) := by norm_num
    _ ≤ panTypeICharSqrtMeanMaxY X q x (fun _ : ℕ => 1) u := by
          exact Finset.le_max'
            (s := (Finset.range (x + 1)).image (fun y => panTypeICharSqrtMean y X q (fun _ : ℕ => 1) u))
            (x := panTypeICharSqrtMean y X q (fun _ : ℕ => 1) u)
            (Finset.mem_image.mpr ⟨y, hy, rfl⟩)

/-- **乘法大筛特征均值输入 (Bombieri--Davenport 装配形式, 开放)**: 对每个
  `A > 0` 存在 `C > 0, B, x₀`, 使对所有 `X ≥ x₀` 与
  `Q := (xX)^{1/2}/log^B(xX)`,

  `Σ_{q ≤ Q} μ²(q)·3^{ω(q)}·φ(q)^{1/2}·max_{y ≤ xX} Σ_{a ≤ X} |f(a)|/|log(y/a)|·(Σ_χ ‖V_χ(y/a)‖²)^{1/2}
     ≤ C·xX/log^A(xX)`.

  这是 `PanTypeICharacterMeanValue` 归约后剩下的唯一解析输入 (经典证明:
  乘法大筛均值定理 + Cauchy--Schwarz 在 q 上的装配 + vaughanFirst 平方和 +
  权重 φ-和 + 外层 (y,a) 权重和; 见 Liu 2022 §III Lemma 1; HR 1974 Ch.10).
  求和到 `q ≤ Q` 的全体特征版本需要原特征分解与 Gauss 和 (见
  `Multiplicative.lean` 模块头红队注记), 保留为开放目标; 对 `|f| ≤ 1` 一致. -/
def panTypeICharMeanSieveBound (x : ℕ → ℝ) (f : ℕ → ℝ) (u : ℕ) : Prop :=
  (∀ a : ℕ, |f a| ≤ 1) ∧
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
      ∀ X : ℕ, x₀ ≤ X →
        ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            Real.sqrt (Nat.totient q : ℝ) * panTypeICharSqrtMeanMaxY X q (Nat.floor (x X)) f u ≤
          C * x X / (log (x X)) ^ A

/-- **乘法大筛均值核心 (Bombieri--Davenport, 文档化, 开放)**:

  `Σ_{q ≤ Q} μ²(q)·3^{ω(q)}·Σ_χ ‖V_χ(m)‖² ≤ C·(m + Q²)·Σ_{n ≤ m} vaughanFirst(n,u)²`.

  经典 Bombieri--Davenport 定理 (Montgomery 1971 Ch.1; Iwaniec--Kowalski 2004
  Ch.7) 需要原特征分解与 Gauss 和 (`|τ(χ)|² = q`), 本仓库 `Multiplicative.lean`
  的红队注记已说明直接叠加 Parseval 路线不成立; 保留为开放目标. 类此地加上
  vaughanFirst 平方和 (初等界 `Σ_{n≤m} vaughanFirst(n,u)² ≪ m·log³(m+2)`),
  权重 φ-和 (`Σ_{q≤Q} μ²(q)3^{ω(q)}φ(q) ≪ Q²·log³(Q+2)`) 与外层 (y,a) 权重和
  (对 `y ≤ xX` 一致的 `Σ_{a≤X} |f(a)|/|log(y/a)|·(y/a)^{1/2}·(y/a+Q²)^{1/2}·log³`
  界), 经 Cauchy--Schwarz 在 q 上的装配 (max 保持在外层, 见 §5.1 头部) 即得
  `panTypeICharMeanSieveBound`. -/
def panTypeICharSquareMeanBound (u : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, ∀ m : ℕ,
    (∑ q ∈ Finset.range (Q + 1),
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * panTypeICharSqSum q m u) ≤
      C * ((m : ℝ) + (Q : ℝ) ^ 2) *
        (∑ n ∈ Finset.range (m + 1), (vaughanFirst n u) ^ 2)

/-- **T1' 归约定理**: 乘法大筛特征均值输入 (panTypeICharMeanSieveBound) ⇒
  PanTypeICharacterMeanValue. 全部有限代数 (CS 块, y-max 归约, 权重单调,
  q = 0 零权重) 在此证明; 唯一解析输入是特征均值界本身. -/
theorem PanTypeICharacterMeanValue.of_sieveBound {x : ℕ → ℝ} {f : ℕ → ℝ} {u : ℕ}
    (hS : panTypeICharMeanSieveBound x f u) : PanTypeICharacterMeanValue x f u := by
  rcases hS with ⟨hfb, hBound⟩
  refine ⟨hfb, ?_⟩
  intro A hA
  rcases hBound A hA with ⟨C, hC, B, x₀, hMain⟩
  refine ⟨C, hC, B, x₀, ?_⟩
  intro X hX
  calc
    (∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panTypeIMeanValueMaxY X q (Nat.floor (x X)) f u)
        ≤ ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              Real.sqrt (Nat.totient q : ℝ) * panTypeICharSqrtMeanMaxY X q (Nat.floor (x X)) f u := by
          apply Finset.sum_le_sum
          intro q hq
          exact panTypeI_weighted_maxY_le_weighted_sqrtMean X q (Nat.floor (x X)) f u
    _ ≤ C * x X / (log (x X)) ^ A := hMain X hX


/-! ## 5.2 T2: type II 加权界的同构归约链 (Cauchy--Schwarz 块 + 双线性特征均值输入)

type II 片段 (Vaughan V3, 双线性 `u < d, v < e` 部分) 的加权界完全复刻
§5/§5.1 的 T1/T1' 有限代数链: 把 `apV1`/`vaughanFirst`/`panTypeI*` 换成
`apV3`/`vaughanThird`/`panTypeII*`, 结构同构:

```text
apV3 的等差和 --[charSum_ap 特征展开]--> 特征和 V_chi(y,u,v) = Σ_{n<=y} vaughanThird(n,u,v)*chi(n)
  --[点式界 |apV3| <= φ(q)⁻¹·Σ_χ ||V_χ||]--> 单项三角形归约
  --[l-一致界]--> panPieceMaxL <= panTypeIIDistributionSum
  --[y-max 归约]--> panPieceMaxY <= panTypeIIMeanValueMaxY
  --[权重单调]--> PanTypeIICharacterMeanValue => PanTypeIIWeightedBound
  --[Cauchy--Schwarz 块 (特征个数 = φ(q))]--> panTypeIICharSqSum / panTypeIICharSqrtMeanMaxY
  --[乘法大筛双线性均值输入 panTypeIICharMeanSieveBound]--> PanTypeIICharacterMeanValue.of_sieveBound
```

唯一的剩余解析输入是 `panTypeIICharMeanSieveBound` (Bombieri--Davenport 双线性
均值: 乘法大筛对 `Σ_χ||V_χ||²` 的均值 + vaughanThird 平方和 + Cauchy--Schwarz
在 q 上的装配, 见 Liu 2022 §III; Montgomery 1971 Ch.1). 与 T1' 完全平行,
零 sorry, 全有限代数在此落地.
-/

/-- type II 片段的特征和: V_χ(y,u,v) = Σ_{n ≤ y} vaughanThird(n,u,v)·χ(n) (复值). -/
noncomputable def panTypeIIV3CharSum (q y u v : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.range (y + 1), (vaughanThird n u v : ℂ) * χ (n : ZMod q)

/-- apV3 的特征展开 (复值): (apV3 y q l u v : ℂ) = φ(q)⁻¹·Σ_χ star(χ(l))·V_χ(y,u,v)
    (对单位 l; 由 charSum_ap 直接给出). -/
theorem apV3_charSum {q y u v : ℕ} (hq : 0 < q) {l : ℕ} (hl : IsUnit (l : ZMod q)) :
    (apV3 y q l u v : ℂ) = (Nat.totient q : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, star (χ (l : ZMod q)) * panTypeIIV3CharSum q y u v χ := by
  unfold apV3 panTypeIIV3CharSum
  have hcast : ((∑ n ∈ Finset.range (y + 1),
        (if n ≡ l [MOD q] then vaughanThird n u v else 0) : ℝ) : ℂ) =
      ∑ n ∈ Finset.range (y + 1),
        (vaughanThird n u v : ℂ) * (if n ≡ l [MOD q] then 1 else 0) := by
    calc
      ((∑ n ∈ Finset.range (y + 1),
          (if n ≡ l [MOD q] then vaughanThird n u v else 0) : ℝ) : ℂ)
          = ∑ n ∈ Finset.range (y + 1),
              ((if n ≡ l [MOD q] then vaughanThird n u v else 0 : ℝ) : ℂ) := by
            exact map_sum Complex.ofRealHom
              (fun n => (if n ≡ l [MOD q] then vaughanThird n u v else 0 : ℝ)) (Finset.range (y + 1))
      _ = ∑ n ∈ Finset.range (y + 1),
            (vaughanThird n u v : ℂ) * (if n ≡ l [MOD q] then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro n hn
          by_cases hmod : n ≡ l [MOD q] <;> simp [hmod]
  rw [hcast]
  exact AnalyticNumberTheory.LargeSieve.charSum_ap hq hl (fun n : ℕ => (vaughanThird n u v : ℂ)) y

/-- apV3 点式界: 对单位 l, |apV3 y q l u v| ≤ φ(q)⁻¹·Σ_χ ||V_χ(y,u,v)||. -/
theorem apV3_abs_le {q y u v : ℕ} (hq : 0 < q) {l : ℕ} (hl : IsUnit (l : ZMod q)) :
    |apV3 y q l u v| ≤ (Nat.totient q : ℝ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q y u v χ‖ := by
  have hnorm : ‖(apV3 y q l u v : ℂ)‖ = |apV3 y q l u v| := by
    exact RCLike.norm_ofReal (apV3 y q l u v)
  rw [← hnorm]
  rw [apV3_charSum hq hl]
  calc
    ‖(Nat.totient q : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        star (χ (l : ZMod q)) * panTypeIIV3CharSum q y u v χ‖
        ≤ ‖(Nat.totient q : ℂ)⁻¹‖ * ‖∑ χ : DirichletCharacter ℂ q,
            star (χ (l : ZMod q)) * panTypeIIV3CharSum q y u v χ‖ := by
          exact norm_mul_le _ _
    _ = (Nat.totient q : ℝ)⁻¹ * ‖∑ χ : DirichletCharacter ℂ q,
            star (χ (l : ZMod q)) * panTypeIIV3CharSum q y u v χ‖ := by
          congr 1
          rw [norm_inv, Complex.norm_natCast]
    _ ≤ (Nat.totient q : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          ‖star (χ (l : ZMod q)) * panTypeIIV3CharSum q y u v χ‖ := by
          exact mul_le_mul_of_nonneg_left (norm_sum_le _ _)
            (inv_nonneg.mpr (Nat.cast_nonneg (Nat.totient q)))
    _ ≤ (Nat.totient q : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          ‖panTypeIIV3CharSum q y u v χ‖ := by
          exact mul_le_mul_of_nonneg_left
            (by
              apply Finset.sum_le_sum
              intro χ hχ
              calc
                ‖star (χ (l : ZMod q)) * panTypeIIV3CharSum q y u v χ‖
                    ≤ ‖star (χ (l : ZMod q))‖ * ‖panTypeIIV3CharSum q y u v χ‖ := norm_mul_le _ _
                _ = ‖χ (l : ZMod q)‖ * ‖panTypeIIV3CharSum q y u v χ‖ := by
                      congr 1
                      simpa using (Complex.norm_conj (χ (l : ZMod q)))
                _ = ‖panTypeIIV3CharSum q y u v χ‖ := by
                      rw [charValue_norm_eq_one hl]
                      simp)
            (inv_nonneg.mpr (Nat.cast_nonneg (Nat.totient q)))

/-- **type II 的分布和 (开放引理的对象)**: 对每个 y, 把 a-吸收后的 type II 片段
  加权和归约到的特征均值对象:
  Σ_{a ≤ X} |f(a)|/|log(y/a)| · Σ_χ ‖V_χ(y/a, u, v)‖. -/
noncomputable def panTypeIIDistributionSum (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X,
    |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
      ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖

/-- 分布和非负. -/
theorem panTypeIIDistributionSum_nonneg (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    0 ≤ panTypeIIDistributionSum y X q f u v := by
  unfold panTypeIIDistributionSum
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _))
    (Finset.sum_nonneg (fun χ hχ => norm_nonneg _))

/-- type II 单项的三角形归约: 对互素 a 与单位 l,
  |f(a)·apV3(y/a; q, a⁻¹l; u, v)/log(y/a)| ≤ |f(a)|/|log(y/a)| · Σ_χ ‖V_χ(y/a, u, v)‖
  (特征展开点式界 + φ(q)⁻¹ ≤ 1). -/
private lemma panTypeII_summand_abs_le (y _X q : ℕ) (f : ℕ → ℝ) (u v a l : ℕ)
    (hq : 0 < q) (hcop : a.Coprime q) (hl : l.Coprime q) :
    |f a * (apV3 (y / a) q (natInvMod q a * l % q) u v / Real.log ((y / a : ℕ) : ℝ))|
      ≤ |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖ := by
  calc
    |f a * (apV3 (y / a) q (natInvMod q a * l % q) u v / Real.log ((y / a : ℕ) : ℝ))|
        = |f a| * |apV3 (y / a) q (natInvMod q a * l % q) u v / Real.log ((y / a : ℕ) : ℝ)| := by
          rw [abs_mul]
    _ = |f a| * (|apV3 (y / a) q (natInvMod q a * l % q) u v| / |Real.log ((y / a : ℕ) : ℝ)|) := by
          rw [abs_div]
    _ ≤ |f a| * (((Nat.totient q : ℝ)⁻¹ *
            ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖) /
            |Real.log ((y / a : ℕ) : ℝ)|) := by
          have h1 : |apV3 (y / a) q (natInvMod q a * l % q) u v| ≤
              (Nat.totient q : ℝ)⁻¹ *
                ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖ :=
            apV3_abs_le (q := q) (y := y / a) (u := u) (v := v) hq
              (isUnit_natInvMod_mul_residue hq hcop hl)
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 (abs_nonneg _)) (abs_nonneg _)
    _ = |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          ((Nat.totient q : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖) := by
          ring
    _ ≤ |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖) := by
          have hqpos : 0 < (Nat.totient q : ℝ) := by
            exact_mod_cast (Nat.totient_pos.mpr hq)
          have hq1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
            exact_mod_cast (Nat.succ_le_of_lt (Nat.totient_pos.mpr hq))
          have hφ : (Nat.totient q : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hqpos).mpr hq1
          have hS : 0 ≤ (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖) := by
            apply Finset.sum_nonneg
            intro χ hχ
            exact norm_nonneg _
          have hPhiS : (Nat.totient q : ℝ)⁻¹ *
                (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖) ≤
              (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖) := by
            simpa using (mul_le_mul_of_nonneg_right hφ hS)
          exact mul_le_mul_of_nonneg_left hPhiS
            (div_nonneg (abs_nonneg _) (abs_nonneg _))

/-- **type II 的 l-一致归约**: 对单位 l, 每个 |panPieceSum y X q l f g| 被
  panTypeIIDistributionSum 一致控制 (界与 l 无关). -/
theorem panPieceSum_typeII_abs_le (y X q : ℕ) (f : ℕ → ℝ) (u v l : ℕ) (hq : 0 < q)
    (hl : l.Coprime q) :
    |panPieceSum y X q l f (fun y' q' l' => apV3 y' q' l' u v / Real.log (y' : ℝ))|
      ≤ panTypeIIDistributionSum y X q f u v := by
  calc
    |panPieceSum y X q l f (fun y' q' l' => apV3 y' q' l' u v / Real.log (y' : ℝ))|
        ≤ ∑ a ∈ Finset.Icc 1 X,
            |if a.Coprime q then
              f a * (apV3 (y / a) q (natInvMod q a * l % q) u v / Real.log ((y / a : ℕ) : ℝ))
            else 0| := by
          unfold panPieceSum
          exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Finset.Icc 1 X,
          |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
            ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖ := by
          apply Finset.sum_le_sum
          intro a ha
          by_cases hcop : a.Coprime q
          · rw [if_pos hcop]
            exact panTypeII_summand_abs_le y X q f u v a l hq hcop hl
          · have hnonneg : 0 ≤ |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
                ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖ := by
              exact mul_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _))
                (Finset.sum_nonneg (fun χ hχ => norm_nonneg _))
            simp [hcop]
            exact hnonneg

/-- **l-max 归约**: panPieceMaxL ≤ panTypeIIDistributionSum (界与 l 无关, 故 max 直接进入). -/
theorem panPieceMaxL_le_typeIIDistributionSum (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    panPieceMaxL y X q f (fun y' q' l' => apV3 y' q' l' u v / Real.log (y' : ℝ)) ≤
      panTypeIIDistributionSum y X q f u v := by
  unfold panPieceMaxL
  by_cases hS : ((Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q)).Nonempty
  · dsimp only []
    rw [dif_pos hS]
    apply Finset.max'_le
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨l, hl, rfl⟩
    have hlS : l ∈ (Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q) := hl
    have hl' : l.Coprime q := (Finset.mem_filter.mp hlS).2
    have hlIcc : l ∈ Finset.Icc 1 (q - 1) := (Finset.mem_filter.mp hlS).1
    have hq : 0 < q := by
      have h1 : 1 ≤ l := (Finset.mem_Icc.mp hlIcc).1
      have h2 : l ≤ q - 1 := (Finset.mem_Icc.mp hlIcc).2
      omega
    exact panPieceSum_typeII_abs_le y X q f u v l hq hl'
  · rw [dif_neg hS]
    exact panTypeIIDistributionSum_nonneg y X q f u v

/-- **特征均值对象的 y-max**: 镜像 panTypeIMeanValueMaxY. -/
noncomputable def panTypeIIMeanValueMaxY (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  ((Finset.range (x + 1)).image (fun y => panTypeIIDistributionSum y X q f u v)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- **y-max 归约**: panPieceMaxY ≤ panTypeIIMeanValueMaxY (逐 y 的
  panPieceMaxL ≤ panTypeIIDistributionSum 后取 max). -/
theorem panPieceMaxY_le_typeIIMeanValueMaxY (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    panPieceMaxY X q x f (fun y' q' l' => apV3 y' q' l' u v / Real.log (y' : ℝ)) ≤
      panTypeIIMeanValueMaxY X q x f u v := by
  unfold panPieceMaxY panTypeIIMeanValueMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  exact le_trans (panPieceMaxL_le_typeIIDistributionSum y X q f u v)
    (Finset.le_max'
      (s := (Finset.range (x + 1)).image (fun y => panTypeIIDistributionSum y X q f u v))
      (x := panTypeIIDistributionSum y X q f u v)
      (Finset.mem_image.mpr ⟨y, hy, rfl⟩))

/-- **开放引理 T2' (特征均值界)**: type II 的剩余分析输入 — 在 3^{ω(q)} 权重下
  特征均值对象的界 (对 |f| ≤ 1 一致; 经典证明: 乘法大筛对 Σ_χ||V_χ||² 的均值
  + Cauchy-Schwarz 装配). 这是 PanTypeIIWeightedBound 归约后剩下的唯一解析台阶. -/
def PanTypeIICharacterMeanValue (x : ℕ → ℝ) (f : ℕ → ℝ) (u v : ℕ) : Prop :=
  (∀ a : ℕ, |f a| ≤ 1) ∧
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
      ∀ X : ℕ, x₀ ≤ X →
        ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            panTypeIIMeanValueMaxY X q (Nat.floor (x X)) f u v ≤
          C * x X / (log (x X)) ^ A

/-- **T2 归约定理**: PanTypeIICharacterMeanValue (特征均值, 开放) ⇒
  PanTypeIIWeightedBound (加权 type II 界). 全部有限代数 (特征展开, 点式界,
  l-max/y-max 归约, 权重单调) 在此证明; 剩下的唯一解析输入是特征均值界本身. -/
theorem PanTypeIIWeightedBound.of_characterMeanValue {x : ℕ → ℝ} {f : ℕ → ℝ} {u v : ℕ} :
    PanTypeIICharacterMeanValue x f u v → PanTypeIIWeightedBound x f u v := by
  intro hP
  rcases hP with ⟨hfb, hBound⟩
  intro A hA
  rcases hBound A hA with ⟨C, hC, B, x₀, hMain⟩
  refine ⟨C, hC, B, x₀, ?_⟩
  intro X hX
  calc
    (∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panPieceMaxY X q (Nat.floor (x X)) f
            (fun y q l => apV3 y q l u v / Real.log (y : ℝ)))
        ≤ ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              panTypeIIMeanValueMaxY X q (Nat.floor (x X)) f u v := by
          apply Finset.sum_le_sum
          intro q hq
          have hw : 0 ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card := by
            exact mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num) _)
          exact mul_le_mul_of_nonneg_left
            (panPieceMaxY_le_typeIIMeanValueMaxY X q (Nat.floor (x X)) f u v) hw
    _ ≤ C * x X / (log (x X)) ^ A := hMain X hX

/-- 特征和的 L² 对象: t_q(m) = Σ_χ ‖V_χ(m)‖² (乘法大筛均值的自然对象). -/
noncomputable def panTypeIICharSqSum (q m u v : ℕ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q m u v χ‖ ^ 2

/-- **Cauchy--Schwarz 块**: Σ_χ ‖V_χ(m)‖ ≤ φ(q)^{1/2}·(Σ_χ ‖V_χ(m)‖²)^{1/2},
  由特征个数 = φ(q) 与标准 `(Σa_i)² ≤ n·Σa_i²` 给出. -/
theorem panTypeII_charAbsSum_le_cs (q m u v : ℕ) (hq : 0 < q) :
    (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q m u v χ‖) ≤
      Real.sqrt (Nat.totient q : ℝ) * Real.sqrt (panTypeIICharSqSum q m u v) := by
  haveI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ) :=
    AnalyticNumberTheory.LargeSieve.complexHasEnoughRootsOfUnity (Monoid.exponent (ZMod q)ˣ)
      (Monoid.exponent_ne_zero_of_finite (G := (ZMod q)ˣ))
  have hcard : Fintype.card (DirichletCharacter ℂ q) = Nat.totient q := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have hcs : (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q m u v χ‖) ^ 2 ≤
      (Nat.totient q : ℝ) * panTypeIICharSqSum q m u v := by
    calc
      (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q m u v χ‖) ^ 2
          ≤ (Fintype.card (DirichletCharacter ℂ q) : ℝ) *
              (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q m u v χ‖ ^ 2) := by
            simpa using (sq_sum_le_card_mul_sum_sq
              (s := (Finset.univ : Finset (DirichletCharacter ℂ q)))
              (f := fun χ : DirichletCharacter ℂ q => ‖panTypeIIV3CharSum q m u v χ‖))
      _ = (Nat.totient q : ℝ) * panTypeIICharSqSum q m u v := by
            rw [hcard, panTypeIICharSqSum]
  have hS : 0 ≤ panTypeIICharSqSum q m u v := by
    unfold panTypeIICharSqSum
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hφ : 0 ≤ (Nat.totient q : ℝ) := by positivity
  have hsq : (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q m u v χ‖) ^ 2 ≤
      (Real.sqrt (Nat.totient q : ℝ) * Real.sqrt (panTypeIICharSqSum q m u v)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hφ, Real.sq_sqrt hS]
    exact hcs
  exact le_of_sq_le_sq hsq (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- 分布和的逐 a 加权 CS 归约:
  panTypeIIDistributionSum y X q f u v ≤ φ(q)^{1/2}·Σ_{a ≤ X} |f(a)|/|log(y/a)|·t_q(y/a)^{1/2}. -/
theorem panTypeIIDistributionSum_le_csWeighted (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) (hq : 0 < q) :
    panTypeIIDistributionSum y X q f u v ≤
      Real.sqrt (Nat.totient q : ℝ) *
        (∑ a ∈ Finset.Icc 1 X,
          |f a| / |Real.log ((y / a : ℕ) : ℝ)| * Real.sqrt (panTypeIICharSqSum q (y / a) u v)) := by
  unfold panTypeIIDistributionSum
  calc
    (∑ a ∈ Finset.Icc 1 X,
        |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          ∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q (y / a) u v χ‖)
        ≤ ∑ a ∈ Finset.Icc 1 X,
            |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
              (Real.sqrt (Nat.totient q : ℝ) * Real.sqrt (panTypeIICharSqSum q (y / a) u v)) := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (panTypeII_charAbsSum_le_cs q (y / a) u v hq)
            (div_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = Real.sqrt (Nat.totient q : ℝ) *
          (∑ a ∈ Finset.Icc 1 X,
            |f a| / |Real.log ((y / a : ℕ) : ℝ)| * Real.sqrt (panTypeIICharSqSum q (y / a) u v)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          ring

/-- 特征平方和加权对象的逐 y 切片 (乘法大筛均值输入的 y 分量):
  W(y) = Σ_{a ≤ X} |f(a)|/|log(y/a)|·t_q(y/a)^{1/2}. -/
noncomputable def panTypeIICharSqrtMean (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X,
    |f a| / |Real.log ((y / a : ℕ) : ℝ)| * Real.sqrt (panTypeIICharSqSum q (y / a) u v)

/-- 特征平方和加权对象的 y-max (乘法大筛均值输入): 镜像 panTypeICharSqrtMeanMaxY. -/
noncomputable def panTypeIICharSqrtMeanMaxY (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) : ℝ :=
  ((Finset.range (x + 1)).image (fun y => panTypeIICharSqrtMean y X q f u v)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- **y-max 归约**: panTypeIIMeanValueMaxY ≤ φ(q)^{1/2}·panTypeIICharSqrtMeanMaxY
  (逐 y 的加权 CS 后取 max). -/
theorem panTypeIIMeanValueMaxY_le_charSqrtMeanMaxY (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) (hq : 0 < q) :
    panTypeIIMeanValueMaxY X q x f u v ≤
      Real.sqrt (Nat.totient q : ℝ) * panTypeIICharSqrtMeanMaxY X q x f u v := by
  unfold panTypeIIMeanValueMaxY panTypeIICharSqrtMeanMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  calc
    panTypeIIDistributionSum y X q f u v
        ≤ Real.sqrt (Nat.totient q : ℝ) * panTypeIICharSqrtMean y X q f u v :=
          panTypeIIDistributionSum_le_csWeighted y X q f u v hq
    _ ≤ Real.sqrt (Nat.totient q : ℝ) * panTypeIICharSqrtMeanMaxY X q x f u v := by
          exact mul_le_mul_of_nonneg_left
            (Finset.le_max'
              (s := (Finset.range (x + 1)).image (fun y => panTypeIICharSqrtMean y X q f u v))
              (x := panTypeIICharSqrtMean y X q f u v)
              (Finset.mem_image.mpr ⟨y, hy, rfl⟩))
            (Real.sqrt_nonneg _)

/-- 权重非负: μ²(q)·3^{ω(q)} ≥ 0. -/
theorem panTypeII_weight_nonneg (q : ℕ) :
    0 ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card := by
  exact mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num) _)

/-- 带权重的逐 q 归约: w_q·M_q ≤ w_q·φ(q)^{1/2}·W_q (q = 0 时权重为 0, 平凡). -/
private lemma panTypeII_weighted_maxY_le_weighted_sqrtMean (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * panTypeIIMeanValueMaxY X q x f u v ≤
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
        Real.sqrt (Nat.totient q : ℝ) * panTypeIICharSqrtMeanMaxY X q x f u v := by
  by_cases hq0 : q = 0
  · subst q
    have hμ : (μ 0 : ℤ) = 0 := by
      exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree (not_squarefree_zero)
    simp [hμ, Nat.totient_zero]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    calc
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * panTypeIIMeanValueMaxY X q x f u v
          ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              (Real.sqrt (Nat.totient q : ℝ) * panTypeIICharSqrtMeanMaxY X q x f u v) := by
            exact mul_le_mul_of_nonneg_left
              (panTypeIIMeanValueMaxY_le_charSqrtMeanMaxY X q x f u v hq)
              (panTypeII_weight_nonneg q)
      _ = ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            Real.sqrt (Nat.totient q : ℝ) * panTypeIICharSqrtMeanMaxY X q x f u v := by
            ring

/-- **|f| ≤ 1 简化**: |f(a)| ≤ 1 时, 特征平方和加权对象的 y-max 被
  f ≡ 1 的版本一致控制. -/
theorem panTypeIICharSqrtMeanMaxY_le_of_abs_le_one (X q x : ℕ) (u v : ℕ) {f : ℕ → ℝ}
    (hfb : ∀ a : ℕ, |f a| ≤ 1) :
    panTypeIICharSqrtMeanMaxY X q x f u v ≤ panTypeIICharSqrtMeanMaxY X q x (fun _ : ℕ => 1) u v := by
  unfold panTypeIICharSqrtMeanMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  calc
    panTypeIICharSqrtMean y X q f u v
        ≤ panTypeIICharSqrtMean y X q (fun _ : ℕ => 1) u v := by
          unfold panTypeIICharSqrtMean
          apply Finset.sum_le_sum
          intro a ha
          have hdiv : |f a| / |Real.log ((y / a : ℕ) : ℝ)| ≤
              (1 : ℝ) / |Real.log ((y / a : ℕ) : ℝ)| :=
            div_le_div_of_nonneg_right (hfb a) (abs_nonneg _)
          have hsqrt : 0 ≤ Real.sqrt (panTypeIICharSqSum q (y / a) u v) := Real.sqrt_nonneg _
          calc
            |f a| / |Real.log ((y / a : ℕ) : ℝ)| * Real.sqrt (panTypeIICharSqSum q (y / a) u v)
                ≤ (1 : ℝ) / |Real.log ((y / a : ℕ) : ℝ)| *
                    Real.sqrt (panTypeIICharSqSum q (y / a) u v) :=
                  mul_le_mul_of_nonneg_right hdiv hsqrt
            _ = |(1 : ℝ)| / |Real.log ((y / a : ℕ) : ℝ)| *
                  Real.sqrt (panTypeIICharSqSum q (y / a) u v) := by norm_num
    _ ≤ panTypeIICharSqrtMeanMaxY X q x (fun _ : ℕ => 1) u v := by
          exact Finset.le_max'
            (s := (Finset.range (x + 1)).image (fun y => panTypeIICharSqrtMean y X q (fun _ : ℕ => 1) u v))
            (x := panTypeIICharSqrtMean y X q (fun _ : ℕ => 1) u v)
            (Finset.mem_image.mpr ⟨y, hy, rfl⟩)

/-- **乘法大筛双线性特征均值输入 (Bombieri--Davenport 装配形式, 开放)**: 对每个
  `A > 0` 存在 `C > 0, B, x₀`, 使对所有 `X ≥ x₀` 与 `Q := (xX)^{1/2}/log^B(xX)`,

  `Σ_{q ≤ Q} μ²(q)·3^{ω(q)}·φ(q)^{1/2}·max_{y ≤ xX} Σ_{a ≤ X} |f(a)|/|log(y/a)|·(Σ_χ ‖V_χ(y/a)‖²)^{1/2}
     ≤ C·xX/log^A(xX)`.

  这是 `PanTypeIICharacterMeanValue` 归约后剩下的唯一解析输入 (经典证明:
  乘法大筛均值定理 + Cauchy--Schwarz 在 q 上的装配 + vaughanThird 平方和 +
  权重 φ-和 + 外层 (y,a) 权重和; 见 Liu 2022 §III; Montgomery 1971 Ch.1;
  HR 1974 Ch.10). 对 `|f| ≤ 1` 一致. -/
def panTypeIICharMeanSieveBound (x : ℕ → ℝ) (f : ℕ → ℝ) (u v : ℕ) : Prop :=
  (∀ a : ℕ, |f a| ≤ 1) ∧
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
      ∀ X : ℕ, x₀ ≤ X →
        ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            Real.sqrt (Nat.totient q : ℝ) * panTypeIICharSqrtMeanMaxY X q (Nat.floor (x X)) f u v ≤
          C * x X / (log (x X)) ^ A

/-- **乘法大筛双线性均值核心 (Bombieri--Davenport, 文档化, 开放)**:

  `Σ_{q ≤ Q} μ²(q)·3^{ω(q)}·Σ_χ ‖V_χ(m)‖² ≤ C·(m + Q²)·Σ_{n ≤ m} vaughanThird(n,u,v)²`.

  经典 Bombieri--Davenport 定理 (Montgomery 1971 Ch.1; Iwaniec--Kowalski 2004
  Ch.7) 需要原特征分解与 Gauss 和; type II 双线性结构在 Vaughan 恒等式中按
  d,e 展开后进入大筛均值 (Liu 2022 §III), 保留为开放目标. -/
def panTypeIICharSquareMeanBound (u v : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, ∀ m : ℕ,
    (∑ q ∈ Finset.range (Q + 1),
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * panTypeIICharSqSum q m u v) ≤
      C * ((m : ℝ) + (Q : ℝ) ^ 2) *
        (∑ n ∈ Finset.range (m + 1), (vaughanThird n u v) ^ 2)

/-- **T2' 归约定理**: 乘法大筛双线性特征均值输入 (panTypeIICharMeanSieveBound) ⇒
  PanTypeIICharacterMeanValue. 全部有限代数 (CS 块, y-max 归约, 权重单调,
  q = 0 零权重) 在此证明; 唯一解析输入是特征均值界本身. -/
theorem PanTypeIICharacterMeanValue.of_sieveBound {x : ℕ → ℝ} {f : ℕ → ℝ} {u v : ℕ}
    (hS : panTypeIICharMeanSieveBound x f u v) : PanTypeIICharacterMeanValue x f u v := by
  rcases hS with ⟨hfb, hBound⟩
  refine ⟨hfb, ?_⟩
  intro A hA
  rcases hBound A hA with ⟨C, hC, B, x₀, hMain⟩
  refine ⟨C, hC, B, x₀, ?_⟩
  intro X hX
  calc
    (∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panTypeIIMeanValueMaxY X q (Nat.floor (x X)) f u v)
        ≤ ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (log (x X)) ^ B) + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              Real.sqrt (Nat.totient q : ℝ) * panTypeIICharSqrtMeanMaxY X q (Nat.floor (x X)) f u v := by
          apply Finset.sum_le_sum
          intro q hq
          exact panTypeII_weighted_maxY_le_weighted_sqrtMean X q (Nat.floor (x X)) f u v
    _ ≤ C * x X / (log (x X)) ^ A := hMain X hX

end

end AnalyticNumberTheory.Sieve
