import AnalyticNumberTheory.Sieve.PanMainTerm
import Mathlib.Tactic

/-!
# S3 W1 子台阶: 引理 C — `Σ_{d ≤ Q} μ²(d)·2^{ω(d)}/d ≤ C·(log(Q+2))²`

与 `panMainTotientWeightedSum_le_polylog` (W3, PanMainTerm.lean §4) 完全同构.
对平方自由 `d`, 单项 `μ²(d)·2^{ω(d)}/d = ∏_{p | d} 2/p` (这里 `d = ∏_{p|d} p`,
`2^{ω(d)} = ∏_{p|d} 2`), 子集展开
`Σ_{q ≤ Q, sqfree} ∏_{p|q} c p ≤ ∏_{p ≤ Q} (1 + c p)` 代入 `c p = 2/p`,
`∏(1+u) ≤ exp(Σu)` (`Real.prod_one_add_le_exp_sum`), 恒等式
`Σ_{p ≤ Q} 2/p = 2·Σ_{p ≤ Q} 1/p`, 最后 Mertens 第二定理 (`mertensSecond_nat`):
`Σ_{p ≤ Q} 1/p ≤ log log Q + O(1)`.

组合: `rexp(2·(log log Q + K)) = e^{2K}·(log Q)² ≤ C·(log(Q+2))²`.
有限初段 (`Q ≤ 2`, 和 ≤ 2) 吸收进常数.
-/

namespace AnalyticNumberTheory.Sieve

open Finset Real
open AnalyticNumberTheory.Mertens
open scoped Classical
open scoped ArithmeticFunction.Moebius

/-- 二幂权重和: `Σ_{d ≤ Q} μ²(d)·2^{ω(d)}/d` (W1 引理 C 的 LHS). -/
noncomputable def sumTwoPowWeighted (Q : ℕ) : ℝ :=
  ∑ d ∈ Finset.range (Q + 1),
    ((μ d : ℤ) : ℝ) ^ 2 * (2 : ℝ) ^ d.primeFactors.card / (d : ℝ)

/-- 平方自由 d 的主项权重: `μ²(d) = 1`, `2^{ω(d)} = ∏_{p|d} 2`, `d = ∏_{p|d} p`,
故单项 = `∏_{p | d} 2/p`. -/
theorem sumTwoPowWeighted_term_squarefree (d : ℕ) (hd : Squarefree d) :
    ((μ d : ℤ) : ℝ) ^ 2 * (2 : ℝ) ^ d.primeFactors.card / (d : ℝ) =
      ∏ p ∈ d.primeFactors, (2 : ℝ) / (p : ℝ) := by
  have hmu : ((μ d : ℤ) : ℝ) ^ 2 = 1 := by
    rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hd]
    norm_num
  have hprod : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    rw [squarefree_eq_prod_primeFactors hd, Nat.cast_prod]
  calc
    ((μ d : ℤ) : ℝ) ^ 2 * (2 : ℝ) ^ d.primeFactors.card / (d : ℝ)
        = (2 : ℝ) ^ d.primeFactors.card / (∏ p ∈ d.primeFactors, (p : ℝ)) := by
          rw [hmu, hprod]
          norm_num
    _ = (∏ p ∈ d.primeFactors, (2 : ℝ)) / (∏ p ∈ d.primeFactors, (p : ℝ)) := by
          rw [← Finset.prod_const]
    _ = ∏ p ∈ d.primeFactors, (2 : ℝ) / (p : ℝ) := by
          rw [← Finset.prod_div_distrib]

/-- 非平方自由 d 的权重为零 (`μ(d) = 0`). -/
theorem sumTwoPowWeighted_term_non_squarefree (d : ℕ) (hd : ¬ Squarefree d) :
    ((μ d : ℤ) : ℝ) ^ 2 * (2 : ℝ) ^ d.primeFactors.card / (d : ℝ) = 0 := by
  have hmu : (μ d : ℤ) = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd
  simp [hmu]

/-- 权重非负. -/
private lemma sumTwoPowWeighted_term_nonneg (d : ℕ) :
    0 ≤ ((μ d : ℤ) : ℝ) ^ 2 * (2 : ℝ) ^ d.primeFactors.card / (d : ℝ) := by
  exact div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _))
    (Nat.cast_nonneg d)

/-- 二幂权重和 ≤ 素数 ≤ Q 上的乘积 `∏_{p ≤ Q} (1 + 2/p)` (子集展开, `c p = 2/p`). -/
theorem sumTwoPowWeighted_le_prod_one_add (Q : ℕ) :
    sumTwoPowWeighted Q ≤ ∏ p ∈ primesUpTo Q, (1 + (2 : ℝ) / (p : ℝ)) := by
  unfold sumTwoPowWeighted
  calc
    (∑ d ∈ Finset.range (Q + 1),
        ((μ d : ℤ) : ℝ) ^ 2 * (2 : ℝ) ^ d.primeFactors.card / (d : ℝ))
        = ∑ d ∈ Finset.range (Q + 1),
            if Squarefree d then
              ((μ d : ℤ) : ℝ) ^ 2 * (2 : ℝ) ^ d.primeFactors.card / (d : ℝ)
            else 0 := by
          apply Finset.sum_congr rfl
          intro d hd
          by_cases h : Squarefree d
          · rw [if_pos h]
          · rw [if_neg h]
            exact sumTwoPowWeighted_term_non_squarefree d h
    _ = ∑ d ∈ (Finset.range (Q + 1)).filter Squarefree,
          ((μ d : ℤ) : ℝ) ^ 2 * (2 : ℝ) ^ d.primeFactors.card / (d : ℝ) := by
          rw [Finset.sum_filter]
    _ = ∑ d ∈ (Finset.range (Q + 1)).filter Squarefree,
          ∏ p ∈ d.primeFactors, (2 : ℝ) / (p : ℝ) := by
          apply Finset.sum_congr rfl
          intro d hd
          exact sumTwoPowWeighted_term_squarefree d (Finset.mem_filter.mp hd).2
    _ ≤ ∏ p ∈ primesUpTo Q, (1 + (2 : ℝ) / (p : ℝ)) := by
          exact sum_squarefree_prod_primeFactors_le_prod_one_add Q
            (fun p => (2 : ℝ) / (p : ℝ)) (by
              intro p hp
              exact div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg p))

/-- 二幂权重和在 Q 上单调 (权重非负). -/
theorem sumTwoPowWeighted_mono : Monotone sumTwoPowWeighted := by
  intro Q₁ Q₂ hQ
  unfold sumTwoPowWeighted
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hd) (by omega : Q₁ + 1 ≤ Q₂ + 1))
  · intro d hd hnq
    exact sumTwoPowWeighted_term_nonneg d

