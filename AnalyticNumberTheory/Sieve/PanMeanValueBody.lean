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
以及 `3^{ω(q)} = Σ_{d|q} 2^{ω(d)}` 权重打包 (`WeightedPan`). 尚未落地:
type I/type II 界与最终装配 (见 `PAN_PROOF_ATLAS.md` 的路线表, 状态标注).
-/

import AnalyticNumberTheory.Sieve.WeightedPan
import AnalyticNumberTheory.Sieve.VaughanIdentity
import Mathlib.Data.ZMod.Basic
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

end AnalyticNumberTheory.Sieve
