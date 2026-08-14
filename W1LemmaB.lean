import AnalyticNumberTheory.Sieve.PanMainTerm
import AnalyticNumberTheory.Sieve.WeightedPan
import Mathlib.Tactic

/-!
# W1 引理 B (issue #42, S3): 平方自由 q 的 `3^{ω(q)}` 分解

对平方自由 `q` (素因子集 `{p₁, …, p_k}`):

  `3^{ω(q)} = 3^k = ∏_{p | q} (1 + 2) = Σ_{S ⊆ primeFactors q} 2^{|S|}
             = Σ_{d | q, Squarefree d} 2^{ω(d)}`,

其中每个子集 `S ⊆ primeFactors q` 一一对应平方自由因子 `d = ∏_{p ∈ S} p`.

(`WeightedPan.lean` 已有 `ℕ` 版本 `threeOmega_eq_sum_twoOmega_divisors`;
本文件给出 W1 需要的 `ℝ` + 平方自由过滤版本, 并显式分离出两个可复用的步骤:
组合恒等式 `3^k = Σ_{S⊆[k]} 2^{|S|}` 与 子集 ↔ 平方自由因子 双射.)
-/

namespace AnalyticNumberTheory.Sieve

open Finset Real
open scoped BigOperators

/-- **组合恒等式**: `Σ_{u ∈ t.powerset} 2^{|u|} = 3^{|t|}` (即 `(1 + 2)^{|t|}`
按子集展开; 每个元素独立选择"在子集中 / 不在", 权重 2 与 1). -/
theorem sum_powerset_two_pow_eq_three_pow {α : Type*} [DecidableEq α] (t : Finset α) :
    (∑ u ∈ t.powerset, (2 : ℝ) ^ u.card) = (3 : ℝ) ^ t.card := by
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
      have hcard : (∑ u ∈ s.powerset, (2 : ℝ) ^ (insert a u).card) =
          ∑ u ∈ s.powerset, (2 : ℝ) ^ u.card * 2 := by
        apply Finset.sum_congr rfl
        intro u hu
        have hua : a ∉ u := fun hx => ha ((Finset.mem_powerset.mp hu) hx)
        rw [Finset.card_insert_of_notMem hua, pow_succ]
      rw [hcard, ← Finset.sum_mul, ih, Finset.card_insert_of_notMem ha, pow_succ]
      ring

end AnalyticNumberTheory.Sieve
