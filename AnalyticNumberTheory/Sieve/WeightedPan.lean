/-
! # AnalyticNumberTheory.Sieve.WeightedPan

## 加权 Pan--Bombieri--Vinogradov 输入 (Weighted Pan-BV input)

陈氏定理的 Ω 上界 (以及一般 Goldbach 型筛法) 需要的不是逐模数一致分布界,
而是带 `3^{ω(d)}` 权重的**平均**分布条件: 对每个 `A > 0` 存在一致常数 `C`,
使得

  Σ_{d | P} 3^{ω(d)} · |Δ(d)| ≤ C · x / log^A x,

其中 `Δ(d)` 是同余计数与主项 `ν(d)·x/log x` 的差. 权重 `3^{ω(d)}` 的来源是
Selberg 上界筛展开中 `[d₁,d₂] = d` 的 (d₁,d₂) 对数 (见 `lcmPairCount`).

本模块把这一输入做成可复用的统一接口:

1. **权重来源** — `lcmPairCount` / `lcmPairWeightedSum`:
   squarefree `d` 上 `3^{ω(d)}` 恰为满足 `[d₁,d₂] = d` 的对数; 由此
   `Σ_{d|Q} 3^{ω(d)}·f(d) = Σ_{d₁|Q} Σ_{d₂|Q} f([d₁,d₂])`,
   这是 Selberg 双重和打包成单重加权和的精确有限代数.

2. **消费侧接口** — `WeightedPanCondition`: 对任意 `BoundingSieve` 族 `S N`
   与尺度 `x N`, 陈述均匀加权分布条件. 陈氏定理实例化为
   `x N = N`、`S N = correctedChenBoundingSieve N`、`w d = 3^{ω(d)}`,
   此时 `S.rem d` 正是同余计数误差
   `|#{p ∈ support, p ≡ N [MOD d]} − ν(d)·N/log N|`.

3. **经典源头定理的精确陈述** — `PanMeanValueUniform`: 经典加权 Pan 均值
   定理 (Pan 1963; 亦见 Halberstam--Richert 1974 Ch.10、Liu 2022 §III):

     ∀ A > 0, ∃ C, B, x₀, ∀ x ≥ x₀:
       Σ_{q ≤ x^{1/2}/log^B x} μ²(q)·3^{ω(q)}·
         max_{0<l<q,(l,q)=1} Σ_{a≤x} f(a)·|Δ(x/a; q, l)| ≤ C·x/log^A x.

   该定理的证明依赖大筛法与 Vaughan 恒等式, 属于研究级开放目标; 本模块只
   固定其精确陈述与所需定义, 不声称已证明. 一旦 `PanMeanValueUniform` (或
   PNT 级主项估计) 被证明, 与 `WeightedPanCondition` 的对接即成为纯解析步骤.

参考:
  - Pan, C.D. (1963), Sci. Sinica 12, 465-473
  - Bombieri, E. (1965), Math. Ann. 157, 220-260
  - Vinogradov, A.I. (1965), Izv. Akad. Nauk SSSR 29, 903-934
  - Halberstam & Richert, "Sieve Methods" (1974), Ch. 10
  - Liu, Z. (2022), arXiv:2203.07871
-/

import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import AnalyticNumberTheory.Sieve.BombieriVinogradov

namespace AnalyticNumberTheory.Sieve

open Finset Real

open scoped Classical
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.omega

/-! ## 1. 权重来源: `3^{ω(d)} = #{(d₁,d₂) | [d₁,d₂] = d}` -/

/-- 对 squarefree 的 `d`, 满足 `lcm d₁ d₂ = d` 且 `d₁,d₂ | d` 的配对
`(d₁,d₂)` 数恰好是 `3^{ω(d)}`: 每个素因子 `p | d` 在 `(d₁,d₂)` 中的幂次
组合有 `(0,1),(1,0),(1,1)` 三种. 这是 Selberg 上界筛中 `3^{ω(d)}` 权重的
精确来源. -/
theorem lcmPairCount (d : ℕ) (hsq : Squarefree d) :
    ((d.divisors ×ˢ d.divisors).filter (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d)).card =
      3 ^ d.primeFactors.card := by
  have hω : d.primeFactors.card = ArithmeticFunction.cardDistinctFactors d := by
    rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
      Nat.toFinset_factors]
  rw [hω, ← Nat.card_pair_lcm_eq hsq]

/-- Squarefree `Q` 的因子之 lcm 仍整除 `Q` (因子分解版本). -/
private theorem lcm_dvd_of_squarefree {Q d₁ d₂ : ℕ} (hQ : Squarefree Q)
    (h₁ : d₁ ∣ Q) (h₂ : d₂ ∣ Q) : Nat.lcm d₁ d₂ ∣ Q := by
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hQpos : 0 < Q := Nat.pos_of_ne_zero hQ0
  have hd₁0 : d₁ ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos h₁ hQpos)
  have hd₂0 : d₂ ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos h₂ hQpos)
  have hlcm0 : Nat.lcm d₁ d₂ ≠ 0 := Nat.lcm_ne_zero hd₁0 hd₂0
  rw [← Nat.factorization_le_iff_dvd hlcm0 hQ0]
  rw [Nat.factorization_lcm hd₁0 hd₂0]
  rw [← Nat.factorization_le_iff_dvd hd₁0 hQ0] at h₁
  rw [← Nat.factorization_le_iff_dvd hd₂0 hQ0] at h₂
  exact sup_le h₁ h₂

/-- **Selberg 双重和打包**: 对 squarefree 筛积 `Q`,

  Σ_{d | Q} 3^{ω(d)} · f(d) = Σ_{d₁ | Q} Σ_{d₂ | Q} f([d₁, d₂]).

权重 `3^{ω(d)}` 正是满足 `[d₁,d₂] = d` 的 `(d₁,d₂)` 对数 (见 `lcmPairCount`);
此恒等式把 Selberg 上界筛的 lcm 双重和精确打包成单重加权和, 是加权 Pan
输入中 `3^{ω(d)}` 权重的有限代数依据. -/
theorem lcmPairWeightedSum (Q : ℕ) (hQ : Squarefree Q) (f : ℕ → ℝ) :
    ∑ d ∈ Q.divisors, (3 : ℝ) ^ d.primeFactors.card * f d =
      ∑ d₁ ∈ Q.divisors, ∑ d₂ ∈ Q.divisors, f (Nat.lcm d₁ d₂) := by
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hQpos : 0 < Q := Nat.pos_of_ne_zero hQ0
  calc
    ∑ d ∈ Q.divisors, (3 : ℝ) ^ d.primeFactors.card * f d
        = ∑ d ∈ Q.divisors,
            ∑ x ∈ (d.divisors ×ˢ d.divisors).filter
                (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d),
              f (Nat.lcm x.1 x.2) := by
            apply Finset.sum_congr rfl
            intro d hd
            have hdvd : d ∣ Q := (Nat.mem_divisors.mp hd).1
            have hd0 : d ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hdvd hQpos)
            have hsqd : Squarefree d := Squarefree.squarefree_of_dvd hdvd hQ
            calc
              (3 : ℝ) ^ d.primeFactors.card * f d
                  = ((d.divisors ×ˢ d.divisors).filter
                        (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d)).card * f d := by
                  rw [lcmPairCount d hsqd, Nat.cast_pow]
                  norm_num
              _ = ∑ x ∈ (d.divisors ×ˢ d.divisors).filter
                      (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d),
                    f d := by
                  simp [Finset.sum_const, nsmul_eq_mul]
              _ = ∑ x ∈ (d.divisors ×ˢ d.divisors).filter
                      (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d),
                    f (Nat.lcm x.1 x.2) := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw [(Finset.mem_filter.mp hx).2]
    _ = ∑ x ∈ Q.divisors.sigma
            (fun d => (d.divisors ×ˢ d.divisors).filter
              (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d)),
          f (Nat.lcm x.2.1 x.2.2) := by
          rw [Finset.sum_sigma]
    _ = ∑ x ∈ Q.divisors ×ˢ Q.divisors, f (Nat.lcm x.1 x.2) := by
          apply Finset.sum_nbij (fun x : (Σ d : ℕ, ℕ × ℕ) => x.2)
          · intro x hx
            rcases Finset.mem_sigma.mp hx with ⟨hxd, hx2⟩
            have hx2' : x.2 ∈ x.1.divisors ×ˢ x.1.divisors ∧
                Nat.lcm x.2.1 x.2.2 = x.1 := Finset.mem_filter.mp hx2
            have hprod : x.2 ∈ x.1.divisors ×ˢ x.1.divisors := hx2'.1
            have hx1dvd : x.1 ∣ Q := (Nat.mem_divisors.mp hxd).1
            have hdvd₁ : x.2.1 ∣ Q :=
              ((Nat.mem_divisors.mp (Finset.mem_product.mp hprod).1).1).trans hx1dvd
            have hdvd₂ : x.2.2 ∣ Q :=
              ((Nat.mem_divisors.mp (Finset.mem_product.mp hprod).2).1).trans hx1dvd
            exact Finset.mem_product.mpr
              ⟨Nat.mem_divisors.mpr ⟨hdvd₁, hQ0⟩, Nat.mem_divisors.mpr ⟨hdvd₂, hQ0⟩⟩
          · intro a₁ ha₁ a₂ ha₂ hpair
            rcases Finset.mem_sigma.mp ha₁ with ⟨_, ha₁₂⟩
            rcases Finset.mem_sigma.mp ha₂ with ⟨_, ha₂₂⟩
            have hlcm₁ : Nat.lcm a₁.2.1 a₁.2.2 = a₁.1 := (Finset.mem_filter.mp ha₁₂).2
            have hlcm₂ : Nat.lcm a₂.2.1 a₂.2.2 = a₂.1 := (Finset.mem_filter.mp ha₂₂).2
            cases a₁ with
            | mk d₁ x₁ =>
              cases a₂ with
            | mk d₂ x₂ =>
                have hx : x₁ = x₂ := by simpa using hpair
                subst x₂
                have hd₁ : d₁ = Nat.lcm x₁.1 x₁.2 := by simpa using hlcm₁.symm
                have hd₂ : d₂ = Nat.lcm x₁.1 x₁.2 := by simpa using hlcm₂.symm
                rw [hd₁, hd₂]
          · intro y hy
            rcases Finset.mem_product.mp hy with ⟨hy₁, hy₂⟩
            have hdvd₁ : y.1 ∣ Q := (Nat.mem_divisors.mp hy₁).1
            have hdvd₂ : y.2 ∣ Q := (Nat.mem_divisors.mp hy₂).1
            have hd₁0 : y.1 ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hdvd₁ hQpos)
            have hd₂0 : y.2 ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hdvd₂ hQpos)
            have hlcm0 : Nat.lcm y.1 y.2 ≠ 0 := Nat.lcm_ne_zero hd₁0 hd₂0
            refine ⟨⟨Nat.lcm y.1 y.2, y⟩, ?_, rfl⟩
            change ⟨Nat.lcm y.1 y.2, y⟩ ∈
              Q.divisors.sigma (fun d => (d.divisors ×ˢ d.divisors).filter
                (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d))
            rw [Finset.mem_sigma]
            constructor
            · exact Nat.mem_divisors.mpr ⟨lcm_dvd_of_squarefree hQ hdvd₁ hdvd₂, hQ0⟩
            · rw [Finset.mem_filter]
              constructor
              · rw [Finset.mem_product]
                constructor
                · exact Nat.mem_divisors.mpr ⟨Nat.dvd_lcm_left y.1 y.2, hlcm0⟩
                · exact Nat.mem_divisors.mpr ⟨Nat.dvd_lcm_right y.1 y.2, hlcm0⟩
              · rfl
          · intro x hx
            rfl
    _ = ∑ d₁ ∈ Q.divisors, ∑ d₂ ∈ Q.divisors, f (Nat.lcm d₁ d₂) := by
          rw [Finset.sum_product]

/-! ## 2. 消费侧接口: 均匀加权分布条件 -/

/-- 筛积除数上的加权余项和 `Σ_{d | P} w(d)·|rem d|`, 其中
`rem d = multSum d − ν(d)·totalMass` 是 `BoundingSieve` 的分布余项. -/
noncomputable def weightedPanRemainder (S : BoundingSieve) (w : ℕ → ℝ) : ℝ :=
  ∑ d ∈ S.prodPrimes.divisors, w d * |S.rem d|

/-- `3^{ω(d)}` 加权的余项和恰为 lcm 双重和: 这是 Selberg 展开中
`Σ_{d₁,d₂} |rem [d₁,d₂]|` 打包成单重加权和的精确形式. -/
theorem weightedPanRemainder_eq_lcmDoubleSum (S : BoundingSieve) :
    weightedPanRemainder S (fun d => (3 : ℝ) ^ d.primeFactors.card) =
      ∑ d₁ ∈ S.prodPrimes.divisors, ∑ d₂ ∈ S.prodPrimes.divisors,
        |S.rem (Nat.lcm d₁ d₂)| := by
  unfold weightedPanRemainder
  exact lcmPairWeightedSum S.prodPrimes S.prodPrimes_squarefree (fun d => |S.rem d|)

/-- 单位权重 Möbius 和的计数筛误差被 `3^{ω(d)}` 加权余项和所控制:
这是 Chen 侧 `correctedChenErrSum_le_panWeighted` 的通用形式. -/
theorem errSum_le_threeOmegaWeightedPanRemainder {S : BoundingSieve} :
    S.errSum (fun _ => 1) ≤
      weightedPanRemainder S (fun d => (3 : ℝ) ^ d.primeFactors.card) := by
  rw [BoundingSieve.errSum, weightedPanRemainder]
  apply Finset.sum_le_sum
  intro d hd
  have hw : (1 : ℝ) ≤ (3 : ℝ) ^ d.primeFactors.card := one_le_pow₀ (by norm_num)
  simpa using le_mul_of_one_le_left (abs_nonneg (S.rem d)) hw

/-- **Selberg Λ² 权重的误差打包**: 对单位有界权重 `w` (`∀ d, |w d| ≤ 1`),
每个 `|Λ²w(d)| ≤ 3^{ω(d)}` (squarefree `d` 上满足 `[d₁,d₂]=d` 的配对数为
`3^{ω(d)}`, 见 `lcmPairCount`), 故

  `errSum(Λ²w) ≤ Σ_{d | P} 3^{ω(d)}·|rem d| = weightedPanRemainder S 3^ω`.

这是经典 Selberg 上界筛误差项 `Σ 3^{ω(d)}|Δ(d)|` 的精确有限形式, 供陈氏
Ω 上界 (chen #7) 把加权 Pan 输入接进 `selberg_upper_bound_sieveProduct`. -/
theorem errSum_lambdaSquared_le_threeOmegaWeightedPanRemainder
    {S : BoundingSieve} {w : ℕ → ℝ} (hw : ∀ d : ℕ, |w d| ≤ 1) :
    S.errSum (BoundingSieve.lambdaSquared w) ≤
      weightedPanRemainder S (fun d => (3 : ℝ) ^ d.primeFactors.card) := by
  rw [BoundingSieve.errSum, weightedPanRemainder]
  apply Finset.sum_le_sum
  intro d hd
  have hsq : Squarefree d := S.squarefree_of_mem_divisors_prodPrimes hd
  have hΛ : |BoundingSieve.lambdaSquared w d| ≤ (3 : ℝ) ^ d.primeFactors.card := by
    unfold BoundingSieve.lambdaSquared
    have hprod : (∑ d₁ ∈ d.divisors, ∑ d₂ ∈ d.divisors,
          if d = Nat.lcm d₁ d₂ then w d₁ * w d₂ else 0) =
        ∑ x ∈ d.divisors ×ˢ d.divisors,
          if d = Nat.lcm x.1 x.2 then w x.1 * w x.2 else 0 := by
      simpa using (Finset.sum_product (s := d.divisors) (t := d.divisors)
        (f := fun p : ℕ × ℕ => if d = Nat.lcm p.1 p.2 then w p.1 * w p.2 else 0)).symm
    rw [hprod]
    calc
      |∑ x ∈ d.divisors ×ˢ d.divisors,
          if d = Nat.lcm x.1 x.2 then w x.1 * w x.2 else 0|
          ≤ ∑ x ∈ d.divisors ×ˢ d.divisors,
              |if d = Nat.lcm x.1 x.2 then w x.1 * w x.2 else 0| := by
              exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ d.divisors ×ˢ d.divisors,
              if d = Nat.lcm x.1 x.2 then (1 : ℝ) else 0 := by
              apply Finset.sum_le_sum
              intro x hx
              by_cases h : d = Nat.lcm x.1 x.2
              · simp [h]
                nlinarith [hw x.1, hw x.2, abs_nonneg (w x.1), abs_nonneg (w x.2),
                  abs_mul (w x.1) (w x.2)]
              · simp [h]
      _ = ((d.divisors ×ˢ d.divisors).filter
              (fun x : ℕ × ℕ => d = Nat.lcm x.1 x.2)).card := by
              rw [← Finset.sum_filter]
              rw [Finset.sum_const]
              simp
      _ = (3 : ℝ) ^ d.primeFactors.card := by
              have hc : ((d.divisors ×ˢ d.divisors).filter
                  (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d)).card = 3 ^ d.primeFactors.card :=
                lcmPairCount d hsq
              have hfilt : (d.divisors ×ˢ d.divisors).filter
                  (fun x : ℕ × ℕ => d = Nat.lcm x.1 x.2) =
                  (d.divisors ×ˢ d.divisors).filter
                    (fun x : ℕ × ℕ => Nat.lcm x.1 x.2 = d) := by
                ext x
                simp [eq_comm]
              rw [hfilt, hc, Nat.cast_pow]
              norm_num
  exact mul_le_mul_of_nonneg_right hΛ (abs_nonneg (S.rem d))

/-- **均匀加权 Pan 分布条件** (消费侧输入): 对每个 `A > 0` 存在一致常数 `C`,
使得对所有充分大的偶数 `N`,

  Σ_{d | P(N)} w(d)·|rem(N,d)| ≤ C · x(N) / log^A x(N).

陈氏定理实例化 (`x N = N`, `S N = correctedChenBoundingSieve N`,
`w d = 3^{ω(d)}`) 时, `S.rem d` 恰为同余计数误差
`|#{p ∈ support, p ≡ N [MOD d]} − ν(d)·N/log N|`, 即 Chen 侧
`CorrectedChenDistributionCondition` 的精确形状; 该条件一旦成立,
`errSum_le_threeOmegaWeightedPanRemainder` 立即给出
`errSum = O(N/log^A N)`. -/
def WeightedPanCondition (x : ℕ → ℝ) (S : ℕ → BoundingSieve) (w : ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 1000 ≤ N → Even N →
      weightedPanRemainder (S N) w ≤ C * x N / (log (x N)) ^ A

/-- 陈氏定理所需的 `3^{ω(d)}` 加权实例. -/
def ThreeOmegaWeightedPanCondition (x : ℕ → ℝ) (S : ℕ → BoundingSieve) : Prop :=
  WeightedPanCondition x S (fun d => (3 : ℝ) ^ d.primeFactors.card)

/-! ## 3. 经典源头定理的精确陈述 -/

/-- π(x/a; q, l): 满足 `p ≤ x/a`、`p` 素数、`p ≡ l [MOD q]` 的素数个数.
这是 Ω 上界误差中按 `a` 缩放的等差数列素数计数. -/
noncomputable def primesUpToDiv (x q l a : ℕ) : ℕ :=
  ((range (x / a + 1)).filter (fun p => p.Prime ∧ p ≡ l [MOD q])).card

/-- Δ(x/a; q, l) = π(x/a; q, l) − li(x/a)/φ(q): 缩放参数的分布误差. -/
noncomputable def weightedDistributionError (x q l a : ℕ) : ℝ :=
  (primesUpToDiv x q l a : ℝ) - logarithmicIntegral (x / a) / Nat.totient q

/-- `f` 加权的模 `q` 误差: `Σ_{a ≤ x} f(a)·|Δ(x/a; q, l)|`. -/
noncomputable def panWeightedError (x q l : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ range (x + 1), f a * |weightedDistributionError x q l a|

/-- `max_{0<l<q,(l,q)=1} panWeightedError x q l f`, 空集 (q ≤ 1) 时取 0. -/
noncomputable def panWeightedErrorMax (x q : ℕ) (f : ℕ → ℝ) : ℝ :=
  let S : Finset ℕ := (Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q)
  if h : S.Nonempty then
    (S.image (fun l => panWeightedError x q l f)).max' (Finset.image_nonempty.mpr h)
  else 0

/-- **经典加权 Pan 均值定理** (研究级开放目标): 对每个 `A > 0` 存在
`C, B, x₀` 使得对所有 `x ≥ x₀`,

  Σ_{q ≤ x^{1/2}/log^B x} μ²(q)·3^{ω(q)}·
    max_{0<l<q,(l,q)=1} Σ_{a≤x} f(a)·|Δ(x/a; q, l)| ≤ C·x/log^A x.

这是陈氏证明中 Ω 误差项 R 的估计工具 (Pan 1963; Halberstam--Richert
1974 Ch.10; Liu 2022 §III). 本陈述只固定精确目标与全部定义; 证明依赖
大筛法与 Vaughan 恒等式, 留作开放研究输入. 一旦证明, 它与
`WeightedPanCondition` 的对接需要额外的主项估计 (PNT 级 `li(x) = x/log x +
O(x/log²x)` 与支撑集截断), 二者皆为标准的解析步骤. -/
def PanMeanValueUniform (x : ℕ → ℝ) (f : ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
    ∀ X : ℕ, x₀ ≤ X →
      ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) /
            (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panWeightedErrorMax X q f ≤
        C * x X / (log (x X)) ^ A

end AnalyticNumberTheory.Sieve
