/-
! # AnalyticNumberTheory.Sieve.VaughanIdentity

## Vaughan 恒等式 (Vaughan's identity)

Vaughan (1977) 把 von Mangoldt 函数 Λ 分解为

  Λ(n) = Σ_{d|n, d≤u} μ(d) log(n/d)
       + Σ_{d|n, u<d} Σ_{e|n/d, e≤v} μ(d) Λ(e)
       + Σ_{d|n, u<d} Σ_{e|n/d, v<e} μ(d) Λ(e).

这是 Bombieri--Vinogradov 定理与加权 Pan 均值定理 (`PanMeanValueUniform`)
证明中的结构性桥梁: 第一项是 type I 型 (截断 μ 与 log 的卷积), 第三项是
type II 型 (两个截断因子的双线性形式), 中间项通过 Möbius 反演重新打包。
本模块只处理**精确有限代数**: 恒等式对任意 `n, u, v` 成立, 不涉及任何
解析估计。

出发点是 mathlib 的 `ArithmeticFunction.moebius_mul_log_eq_vonMangoldt`
(即 `μ * log = Λ`), 再按 `d ≤ u` / `u < d` 与 `e ≤ v` / `v < e` 两层把
卷积和精确切开。

参考:
  - Vaughan, R.C. (1977), Acta Arith. 32, 125-142
  - Halberstam & Richert, "Sieve Methods" (1974), Ch. 9-10
  - Iwaniec & Kowalski, "Analytic Number Theory" (2004), Ch. 13.4
-/

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

namespace AnalyticNumberTheory.Sieve

open Finset
open scoped ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

/-! ## 1. 三个截断项 -/

/-- Type I 主项: `Σ_{d | n, d ≤ u} μ(d) log(n/d)`. -/
noncomputable def vaughanFirst (n u : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ u), ((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ)

/-- 中间项 (type I'): `Σ_{d | n, u < d} Σ_{e | n/d, e ≤ v} μ(d) Λ(e)`. -/
noncomputable def vaughanSecond (n u v : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => u < d),
    ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v), ((μ d : ℤ) : ℝ) * Λ e

/-- Type II 双线性项: `Σ_{d | n, u < d} Σ_{e | n/d, v < e} μ(d) Λ(e)`. -/
noncomputable def vaughanThird (n u v : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => u < d),
    ∑ e ∈ (n / d).divisors.filter (fun e => v < e), ((μ d : ℤ) : ℝ) * Λ e

/-! ## 2. 精确三段恒等式 -/

/-- **Vaughan 恒等式** (精确形式): 对任意 `n u v : ℕ`,

  `Λ n = vaughanFirst n u + vaughanSecond n u v + vaughanThird n u v`.

该等式对截断参数没有任何 `n > u` / `n > v` 假设, 是纯有限卷积代数。 -/
theorem vaughanIdentity (n u v : ℕ) :
    Λ n = vaughanFirst n u + vaughanSecond n u v + vaughanThird n u v := by
  unfold vaughanFirst vaughanSecond vaughanThird
  have hΛ : Λ n = ∑ d ∈ n.divisors, ((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ) := by
    rw [← ArithmeticFunction.moebius_mul_log_eq_vonMangoldt]
    rw [ArithmeticFunction.mul_apply]
    rw [Nat.sum_divisorsAntidiagonal
      (f := fun i j => ((μ : ArithmeticFunction ℝ) i) * ArithmeticFunction.log j)]
    simp only [ArithmeticFunction.intCoe_apply, ArithmeticFunction.log_apply]
  rw [hΛ]
  rw [← Finset.sum_filter_add_sum_filter_not (s := n.divisors) (p := fun d => d ≤ u)]
  have hsplit_not : (∑ d ∈ n.divisors.filter (fun d => ¬ d ≤ u),
        ((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ)) =
      ∑ d ∈ n.divisors.filter (fun d => u < d),
        ((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ) := by
    congr 1
    ext d
    simp [not_le]
  rw [hsplit_not]
  -- 在 `u < d` 部分, 把 `log (n/d)` 换成 `Σ_{e | n/d} Λ e`
  have hlog : (∑ d ∈ n.divisors.filter (fun d => u < d),
        ((μ d : ℤ) : ℝ) * Real.log ((n / d : ℕ) : ℝ)) =
      ∑ d ∈ n.divisors.filter (fun d => u < d),
        ((μ d : ℤ) : ℝ) * (∑ e ∈ (n / d).divisors, Λ e) := by
    congr 1 with d
    rw [← ArithmeticFunction.vonMangoldt_sum (n := n / d)]
  rw [hlog]
  -- 把每个 `e`-和按 `e ≤ v` / `v < e` 切开并分配系数与求和
  have hsplitE : (∑ d ∈ n.divisors.filter (fun d => u < d),
        ((μ d : ℤ) : ℝ) * (∑ e ∈ (n / d).divisors, Λ e)) =
      (∑ d ∈ n.divisors.filter (fun d => u < d),
          ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v), ((μ d : ℤ) : ℝ) * Λ e) +
        (∑ d ∈ n.divisors.filter (fun d => u < d),
          ∑ e ∈ (n / d).divisors.filter (fun e => v < e), ((μ d : ℤ) : ℝ) * Λ e) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    rw [← Finset.sum_filter_add_sum_filter_not (s := (n / d).divisors) (p := fun e => e ≤ v)]
    have hfil : (n / d).divisors.filter (fun e => ¬ e ≤ v) =
        (n / d).divisors.filter (fun e => v < e) := by
      ext e
      simp [not_le]
    rw [hfil]
  rw [hsplitE]
  abel

end

end AnalyticNumberTheory.Sieve
