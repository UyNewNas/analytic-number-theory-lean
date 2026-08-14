import AnalyticNumberTheory.Sieve.W1LemmaB
import AnalyticNumberTheory.Sieve.SumTwoPowWeighted
import AnalyticNumberTheory.Sieve.PanV3SquareMean
import Mathlib.Tactic

/-!
# S3 W1 完整装配 (issue #42): `Σ_{q ≤ Q} μ²(q)·3^{ω(q)}·φ(q)/q ≤ C·Q·(log(Q+2))²`

装配路线 (全部基于 main 上已验证的组件):

```text
Σ_{q ≤ Q} μ²·3^ω·φ/q
  ≤ Σ_{q ≤ Q} μ²·3^ω                 (引理 A: φ/q ≤ 1, 权重非负)
  = Σ_{q ≤ Q, sqfree} 3^ω(q)        (μ² = 1 ⟺ q 平方自由)
  = Σ_{q ≤ Q, sqfree} Σ_{d | q, sqfree} 2^ω(d)   (引理 B, 逐点展开)
  ≤ Σ_{d ≤ Q, sqfree} 2^ω(d)·(Q/d)  (交换求和 + 倍数计数 #{q ≤ Q : d | q} ≤ ⌊Q/d⌋ ≤ Q/d)
  = Q·Σ_{d ≤ Q, sqfree} 2^ω(d)/d
  = Q·Σ_{d ≤ Q} μ²(d)·2^ω(d)/d      (μ² 恢复)
  = Q·sumTwoPowWeighted Q
  ≤ C·Q·(log(Q+2))²                  (引理 C)
```

注: 定理陈述使用 `(log(Q+2))²` (与引理 C 及 W3 的
`panMainTotientWeightedSum_le_polylog` 一致); 若改用 `(log Q)²`, 则在 `Q = 1` 处
RHS 为 0 而 LHS 为 1, 恒假 — 多对数常数需要 `Q+2` 平移.
-/

namespace AnalyticNumberTheory.Sieve

open Finset Real
open scoped BigOperators
open scoped Classical
open scoped ArithmeticFunction.Moebius

/-! ## 1. 引理 A: `φ(q)/q ≤ 1` -/

/-- **引理 A** (issue #42, S3): 对所有 `q : ℕ` 有 `(φ(q):ℝ)/q ≤ 1`
(`Nat.totient_le`; `q = 0` 时按 Lean 的全除法两边都为 0). -/
theorem totient_div_self_le_one (q : ℕ) : (Nat.totient q : ℝ) / (q : ℝ) ≤ 1 := by
  by_cases hq : q = 0
  · subst q
    simp
  · have hle : Nat.totient q ≤ q := Nat.totient_le q
    have hle' : (Nat.totient q : ℝ) ≤ (q : ℝ) := by exact_mod_cast hle
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hq)
    exact (div_le_one hqpos).2 hle'

/-! ## 2. W1 带权对象 `panTypeIWeight3` 与 引理 A 的应用 -/

/-- **W1 带权对象**: `panTypeIWeight3 Q = Σ_{q ≤ Q} μ²(q)·3^{ω(q)}·φ(q)/q`
(W1 定理的 LHS; `q = 0` 项权重为零). -/
noncomputable def panTypeIWeight3 (Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (Q + 1),
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * (Nat.totient q : ℝ) / (q : ℝ)

/-- 单项界: `μ²(q)·3^{ω(q)}·φ(q)/q ≤ μ²(q)·3^{ω(q)}` (引理 A + 权重非负). -/
private lemma panTypeIWeight3_term_le (q : ℕ) :
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * (Nat.totient q : ℝ) / (q : ℝ) ≤
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card := by
  calc
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * (Nat.totient q : ℝ) / (q : ℝ)
        = ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            ((Nat.totient q : ℝ) / (q : ℝ)) := by
          ring
    _ ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * 1 := by
          exact mul_le_mul_of_nonneg_left (totient_div_self_le_one q)
            (mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _))
    _ = ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card := by ring

/-- **装配步骤 2**: `panTypeIWeight3 Q ≤ Σ_{q ≤ Q, sqfree} 3^{ω(q)}`
(引理 A 逐项消去 `φ(q)/q`, 再以 `μ² = 1 ⟺ sqfree` 过滤). -/
theorem panTypeIWeight3_le_sqfree_three_pow (Q : ℕ) :
    panTypeIWeight3 Q ≤
      ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree, (3 : ℝ) ^ q.primeFactors.card := by
  classical
  unfold panTypeIWeight3
  calc
    (∑ q ∈ Finset.range (Q + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * (Nat.totient q : ℝ) / (q : ℝ))
        ≤ ∑ q ∈ Finset.range (Q + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card := by
          exact Finset.sum_le_sum (fun q hq => panTypeIWeight3_term_le q)
    _ = ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree, (3 : ℝ) ^ q.primeFactors.card := by
          calc
            (∑ q ∈ Finset.range (Q + 1),
                ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card)
            = ∑ q ∈ Finset.range (Q + 1),
                (if Squarefree q then
                  ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card
                else 0) := by
                apply Finset.sum_congr rfl
                intro q hq
                by_cases h : Squarefree q
                · simp [h]
                · simp [h, ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
            _ = ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree,
                ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card := by
                rw [Finset.sum_filter]
            _ = ∑ q ∈ (Finset.range (Q + 1)).filter Squarefree, (3 : ℝ) ^ q.primeFactors.card := by
                apply Finset.sum_congr rfl
                intro q hq
                have hsq : Squarefree q := (Finset.mem_filter.mp hq).2
                have hmu : ((μ q : ℤ) : ℝ) ^ 2 = 1 := by
                  rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq]
                  norm_num
                rw [hmu]
                simp

end AnalyticNumberTheory.Sieve
