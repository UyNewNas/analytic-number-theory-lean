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

/-! ## 1b. Pan 权重分解: `3^{ω(q)} = Σ_{d | q} 2^{ω(d)}` -/

/-- 二项式级别的有限和: `Σ_{s ∈ t.powerset} 2^{|s|} = 3^{|t|}`, 即
`(1 + 2)^{|t|}` 按子集大小展开。这是 Pan 权重分解 `3^{ω(q)} = Σ_{d|q} 2^{ω(d)}`
的组合基座 (每个素因子对权重的三种选择 = 它在因子 `d` 中的幂次 ∈ {0, 1} 加上
`2^{ω(d)}` 的两个方向)。 -/
private theorem sum_powerset_pow_two {α : Type*} [DecidableEq α] (t : Finset α) :
    ∑ u ∈ t.powerset, (2 : ℕ) ^ u.card = 3 ^ t.card := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.powerset_insert (s := s) (a := a)]
      have hdisj : Disjoint s.powerset (s.powerset.image (insert a)) := by
        rw [Finset.disjoint_left]
        intro u hu hiu
        have hnu : a ∉ u := fun hx => ha ((Finset.mem_powerset.mp hu) hx)
        rcases Finset.mem_image.mp hiu with ⟨w, hw, rfl⟩
        have hau : a ∈ insert a w := Finset.mem_insert_self a w
        exact hnu hau
      have hinj : Set.InjOn (insert a) (s.powerset : Set (Finset α)) := by
        intro u hu w hw h
        have hua : a ∉ u := fun hx => ha ((Finset.mem_powerset.mp hu) hx)
        have hwa : a ∉ w := fun hx => ha ((Finset.mem_powerset.mp hw) hx)
        have h' := congrArg (fun v : Finset α => v.erase a) h
        simpa [hua, hwa] using h'
      rw [Finset.sum_union hdisj, Finset.sum_image hinj]
      have hcard : (∑ u ∈ s.powerset, (2 : ℕ) ^ (insert a u).card) =
          ∑ u ∈ s.powerset, (2 : ℕ) ^ u.card * 2 := by
        apply Finset.sum_congr rfl
        intro u hu
        have hua : a ∉ u := fun hx => ha ((Finset.mem_powerset.mp hu) hx)
        rw [Finset.card_insert_of_notMem hua, pow_succ]
      rw [hcard, ← Finset.sum_mul, ih, Finset.card_insert_of_notMem ha, pow_succ]
      ring

/-- **Pan 权重分解** (Pan 1963; 亦见 Halberstam--Richert 1974 Lemma 10.3 的
加权形式): 对 squarefree `q`,

  `3^{ω(q)} = Σ_{d | q} 2^{ω(d)} = Σ_{d | q} τ(d)`,

其中最后一个等号来自 squarefree `d` 上 `2^{ω(d)} = τ(d)`. 这是加权 Pan 均值
定理中 `3^{ω(q)}` 权重被外层模数和吸收的关键: `3^{ω(q)}` 展开成对每个素因子
的三种选择, 恰好按 `(d, d 的素因子幂次方向)` 重打包为除数和 `Σ_{d|q} 2^{ω(d)}`. -/
theorem threeOmega_eq_sum_twoOmega_divisors {q : ℕ} (hq : Squarefree q) :
    (3 : ℕ) ^ q.primeFactors.card = ∑ d ∈ q.divisors, (2 : ℕ) ^ d.primeFactors.card := by
  rw [← sum_powerset_pow_two q.primeFactors]
  apply Finset.sum_bij (i := fun s _ => ∏ p ∈ s, p)
  · intro s hs
    rw [Nat.mem_divisors]
    constructor
    · rw [← Nat.prod_primeFactors_of_squarefree hq]
      exact Finset.prod_dvd_prod_of_subset s q.primeFactors (fun p => p)
        (Finset.mem_powerset.mp hs)
    · exact hq.ne_zero
  · intro s₁ hs₁ s₂ hs₂ h
    have hprime₁ : ∀ p ∈ s₁, p.Prime := by
      intro p hp
      exact (Nat.mem_primeFactors.mp ((Finset.mem_powerset.mp hs₁) hp)).1
    have hprime₂ : ∀ p ∈ s₂, p.Prime := by
      intro p hp
      exact (Nat.mem_primeFactors.mp ((Finset.mem_powerset.mp hs₂) hp)).1
    rw [← Nat.primeFactors_prod hprime₁, h, Nat.primeFactors_prod hprime₂]
  · intro d hd
    refine ⟨d.primeFactors, ?_, ?_⟩
    · rw [Finset.mem_powerset]
      exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hq.ne_zero
    · have hsqd : Squarefree d := hq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
      exact Nat.prod_primeFactors_of_squarefree hsqd
  · intro s hs
    have hprime : ∀ p ∈ s, p.Prime := by
      intro p hp
      exact (Nat.mem_primeFactors.mp ((Finset.mem_powerset.mp hs) hp)).1
    rw [Nat.primeFactors_prod hprime]

/-- **Pan 权重重打包**: 对 squarefree `Q`,

  `Σ_{q|Q} 3^{ω(q)} f(q) = Σ_{d|Q} 2^{ω(d)} · Σ_{m|Q/d} f(d·m)`.

这是 `3^{ω(q)} = Σ_{d|q} 2^{ω(d)}` 与整除反链双射 `(q,d) ↔ (d,m=q/d)` 的组合:
外层带 `3^{ω(q)}` 权重的模数和被重打包成带 `2^{ω(d)}` 权重的双层和, 供加权 Pan
均值定理把 `3^{ω(q)}` 吸收进扩大的模数和 (Pan 1963 的经典技巧). -/
theorem threeOmegaWeightedSum_packaging (Q : ℕ) (hQ : Squarefree Q) (f : ℕ → ℝ) :
    (∑ q ∈ Q.divisors, (3 : ℝ) ^ q.primeFactors.card * f q) =
      ∑ d ∈ Q.divisors, (2 : ℝ) ^ d.primeFactors.card *
        (∑ m ∈ (Q / d).divisors, f (d * m)) := by
  rw [Finset.sum_congr rfl (by
    intro q hq
    have hsqq : Squarefree q := hQ.squarefree_of_dvd (Nat.dvd_of_mem_divisors hq)
    have hP : (3 : ℝ) ^ q.primeFactors.card =
        ∑ d ∈ q.divisors, (2 : ℝ) ^ d.primeFactors.card := by
      exact_mod_cast threeOmega_eq_sum_twoOmega_divisors hsqq
    rw [hP, Finset.sum_mul])]
  have hrhs : (∑ d ∈ Q.divisors, (2 : ℝ) ^ d.primeFactors.card *
        (∑ m ∈ (Q / d).divisors, f (d * m))) =
      ∑ d ∈ Q.divisors, ∑ m ∈ (Q / d).divisors, (2 : ℝ) ^ d.primeFactors.card * f (d * m) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
  rw [hrhs]
  rw [← Finset.sum_sigma (s := Q.divisors) (t := fun q => q.divisors)
    (f := fun x => (2 : ℝ) ^ x.2.primeFactors.card * f x.1)]
  rw [← Finset.sum_sigma (s := Q.divisors) (t := fun d => (Q / d).divisors)
    (f := fun x => (2 : ℝ) ^ x.1.primeFactors.card * f (x.1 * x.2))]
  apply Finset.sum_bij (i := fun x _ => ⟨x.2, x.1 / x.2⟩)
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨hq, hd⟩
    have hqQ : x.1 ∣ Q := (Nat.mem_divisors.mp hq).1
    have hQ0 : Q ≠ 0 := (Nat.mem_divisors.mp hq).2
    have hdq : x.2 ∣ x.1 := (Nat.mem_divisors.mp hd).1
    have hdQ : x.2 ∣ Q := dvd_trans hdq hqQ
    rw [Finset.mem_sigma]
    constructor
    · rw [Nat.mem_divisors]
      exact ⟨hdQ, hQ0⟩
    · rw [Nat.mem_divisors]
      constructor
      · exact (Nat.dvd_div_iff_mul_dvd hdQ).2 (by simpa [Nat.mul_div_cancel' hdq] using hqQ)
      · exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hQ0) hdQ)
          (Nat.pos_of_dvd_of_pos hdQ (Nat.pos_of_ne_zero hQ0)))
  · intro a ha b hb h
    rcases Finset.mem_sigma.mp ha with ⟨ha₁, ha₂⟩
    rcases Finset.mem_sigma.mp hb with ⟨hb₁, hb₂⟩
    have hd₁q₁ : a.2 ∣ a.1 := (Nat.mem_divisors.mp ha₂).1
    have hd₂q₂ : b.2 ∣ b.1 := (Nat.mem_divisors.mp hb₂).1
    cases a with
    | mk q₁ d₁ =>
      cases b with
      | mk q₂ d₂ =>
          apply Sigma.ext
          · have hd : d₁ = d₂ := by simpa using congrArg Sigma.fst h
            have hq : q₁ / d₁ = q₂ / d₂ := by simpa using congrArg Sigma.snd h
            calc
              q₁ = d₁ * (q₁ / d₁) := (Nat.mul_div_cancel' hd₁q₁).symm
              _ = d₂ * (q₂ / d₂) := by rw [hq, hd]
              _ = q₂ := Nat.mul_div_cancel' hd₂q₂
          · exact heq_of_eq (by simpa using congrArg Sigma.fst h)
  · intro b hb
    rcases Finset.mem_sigma.mp hb with ⟨hd, hm⟩
    have hdQ : b.1 ∣ Q := (Nat.mem_divisors.mp hd).1
    have hQ0 : Q ≠ 0 := (Nat.mem_divisors.mp hd).2
    have hmQd : b.2 ∣ Q / b.1 := (Nat.mem_divisors.mp hm).1
    have hb1 : b.1 ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hdQ (Nat.pos_of_ne_zero hQ0))
    have hb2 : b.2 ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hmQd
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hQ0) hdQ)
        (Nat.pos_of_dvd_of_pos hdQ (Nat.pos_of_ne_zero hQ0))))
    refine ⟨⟨b.1 * b.2, b.1⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      constructor
      · rw [Nat.mem_divisors]
        constructor
        · exact (Nat.dvd_div_iff_mul_dvd hdQ).1 hmQd
        · exact hQ0
      · rw [Nat.mem_divisors]
        exact ⟨dvd_mul_right b.1 b.2, mul_ne_zero hb1 hb2⟩
    · simp [Nat.mul_div_cancel_left b.2 (Nat.pos_of_ne_zero hb1)]
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨hq, hd⟩
    have hdq : x.2 ∣ x.1 := (Nat.mem_divisors.mp hd).1
    rw [Nat.mul_div_cancel' hdq]

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

/-- π(y; a, q, l): 满足 `p` 素数、`a·p ≤ y`、`a·p ≡ l [MOD q]` 的素数 `p`
个数 (Liu 2022 §II 的精确定义). 这是 Ω 上界误差中按 `a` 缩放、同余在
`a·p` 上的等差数列素数计数; 注意同余条件在乘积 `a·p` 上, 而非 `p` 上. -/
def primesInAPBelow (y a q l : ℕ) : ℕ :=
  ((range (y + 1)).filter (fun p => p.Prime ∧ a * p ≤ y ∧ a * p ≡ l [MOD q])).card

/-- Δ(y; a, q, l) = π(y; a, q, l) − li(y/a)/φ(q): 缩放参数的分布误差. -/
noncomputable def panDistributionError (y a q l : ℕ) : ℝ :=
  (primesInAPBelow y a q l : ℝ) - logarithmicIntegral ((y : ℝ) / a) / Nat.totient q

/-- `f` 加权的模 `q` 分布误差和: `Σ_{(a,q)=1, a ≤ X} f(a)·Δ(y; a, q, l)`
(带符号和, 未取绝对值; 经典 Pan 定理的 `(a,q)=1` 限制是 Liu §IV 修正的关键). -/
noncomputable def panDistributionSum (y X q l : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ range (X + 1), if a.Coprime q then f a * panDistributionError y a q l else 0

/-- `max_{0<l<q,(l,q)=1} |panDistributionSum y X q l f|`, 空集 (q ≤ 1) 时取 0. -/
noncomputable def panMaxL (y X q : ℕ) (f : ℕ → ℝ) : ℝ :=
  let S : Finset ℕ := (Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q)
  if h : S.Nonempty then
    (S.image (fun l => |panDistributionSum y X q l f|)).max' (Finset.image_nonempty.mpr h)
  else 0

/-- `max_{y ≤ x} panMaxL y X q f`: 对截断参数 `y` 的均匀最大值 (Liu Thm 2 的
`max_{y ≤ x}`). -/
noncomputable def panMaxY (X q x : ℕ) (f : ℕ → ℝ) : ℝ :=
  ((Finset.range (x + 1)).image (fun y => panMaxL y X q f)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- **经典加权 Pan 均值定理** (研究级开放目标; Liu 2022 Theorem 2 的精确
形式): 对每个 `A > 0` 存在 `C, B, x₀` 使得对所有 `X ≥ x₀`,

  Σ_{q ≤ (x X)^{1/2}/log^B (x X)} μ²(q)·3^{ω(q)}·
    max_{y ≤ x X} max_{0<l<q,(l,q)=1}
      |Σ_{(a,q)=1, a ≤ X} f(a)·Δ(y; a, q, l)| ≤ C·x X / log^A (x X).

其中 `Δ(y; a, q, l) = π(y; a, q, l) − li(y/a)/φ(q)`. 与旧版陈述的三处差异
(红队审查, 见 `PAN_PROOF_ATLAS.md`): (1) 内和限制 `(a,q)=1`; (2) 加入
`max_{y ≤ x X}`; (3) 绝对值包住整个内和 `|Σ f·Δ|` 而非 `Σ f·|Δ|`. 缺失
(1) 的旧陈述对 Chen 权重 `f` 为假 (Liu §IV 的 `R₁` 修正); `R₁` 依赖 `f` 与
筛积的具体形状, 按边界规则留在 chen 仓库处理.

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
          panMaxY X q (Nat.floor (x X)) f ≤
        C * x X / (log (x X)) ^ A

/-! ## Pan 桥 (ant #25): `PanMeanValueUniform` ⇒ `WeightedPanCondition`

第一步 (a = 1 恒等式): Pan 对象 `primesInAPBelow y a q l` 在 `a = 1` 时
正是普通素数等差计数 `#{p ≤ y : p 素数, p ≡ l [MOD q]}` — 陈氏筛余项
`#{p ∈ support : p ≡ N [MOD d]}` 的分布误差来源. 后续桥引理将把
`WeightedPanCondition` 的筛余项和按此归约到 `panMaxY` 的 `3^{ω(q)}` 加权和. -/

/-- `a = 1` 时缩放计数退化为普通素数等差计数. -/
theorem primesInAPBelow_one (y q l : ℕ) :
    primesInAPBelow y 1 q l =
      ((Finset.range (y + 1)).filter (fun p => p.Prime ∧ p ≡ l [MOD q])).card := by
  unfold primesInAPBelow
  congr 1
  ext p
  constructor
  · intro hp
    rw [Finset.mem_filter] at hp ⊢
    rcases hp with ⟨hp1, hp2⟩
    rcases hp2 with ⟨hpp, hle, hcong⟩
    exact ⟨hp1, ⟨hpp, by simpa using hcong⟩⟩
  · intro hp
    rw [Finset.mem_filter] at hp ⊢
    rcases hp with ⟨hp1, hp2⟩
    rcases hp2 with ⟨hpp, hcong⟩
    exact ⟨hp1, ⟨hpp, ⟨by simpa [one_mul] using
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp1)), by simpa using hcong⟩⟩⟩

/-- `a = 1` 时缩放计数恰为 `primesInAP` (BV 接口的普通等差计数). -/
theorem primesInAPBelow_one_eq_primesInAP (y q l : ℕ) :
    primesInAPBelow y 1 q l = primesInAP y q l := by
  simpa [primesInAP] using primesInAPBelow_one y q l

/-- `a = 1` 时的分布误差 = 普通素数等差误差 `π(y; q, l) − li(y)/φ(q)`. -/
theorem panDistributionError_one (y q l : ℕ) :
    panDistributionError y 1 q l =
      (((Finset.range (y + 1)).filter (fun p => p.Prime ∧ p ≡ l [MOD q])).card : ℝ) -
        logarithmicIntegral (y : ℝ) / Nat.totient q := by
  unfold panDistributionError
  rw [primesInAPBelow_one]
  simp [logarithmicIntegral]

end AnalyticNumberTheory.Sieve
