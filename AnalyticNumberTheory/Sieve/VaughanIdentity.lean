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
open scoped ArithmeticFunction.zeta

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

/-- 经典三段形式的中间项 (type I'): `Σ_{d | n, d ≤ u} Σ_{e | n/d, e ≤ v} μ(d) Λ(e)`. -/
noncomputable def vaughanMiddle (n u v : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ u),
    ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v), ((μ d : ℤ) : ℝ) * Λ e

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

/-! ## 3. 经典三段形式 (n > v) -/

/-- Möbius 和: `Σ_{d | m} μ(d) = [m = 1]`. 由 `μ * ζ = 1` (卷积单位)
与 `coe_mul_zeta_apply` 立即得到. -/
theorem moebiusDivisorSum_eq_ite (m : ℕ) :
    (∑ d ∈ m.divisors, ((μ d : ℤ) : ℝ)) = if m = 1 then 1 else 0 := by
  have h : (((μ : ArithmeticFunction ℝ) * ζ) m) = (1 : ArithmeticFunction ℝ) m := by
    rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simp only [ArithmeticFunction.intCoe_apply] at h
  rw [h, ArithmeticFunction.one_apply]

/-- `e | n`, `n ≠ 0` 时 `n / e = 1 ↔ e = n`. -/
private theorem div_eq_one_iff_eq {n e : ℕ} (he : e ∣ n) (hn : n ≠ 0) :
    n / e = 1 ↔ e = n := by
  constructor
  · intro h
    have hprod : e * (n / e) = n := Nat.mul_div_cancel' he
    simpa [h] using hprod
  · intro rfl
    exact Nat.div_self (Nat.pos_of_ne_zero hn)

/-- **Vaughan 双重和交换**: 把 `Σ_{d|n} Σ_{e|n/d, e≤v} μ(d)Λ(e)` 重新打包为
`Σ_{e|n, e≤v} Λ(e)·Σ_{d|n/e} μ(d)`, 即把 `(d,e)` 对调 (有限整除反链的双射). -/
theorem vaughanDoubleSum_swap (n v : ℕ) :
    (∑ d ∈ n.divisors, ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v),
        ((μ d : ℤ) : ℝ) * Λ e) =
      ∑ e ∈ n.divisors.filter (fun e => e ≤ v),
        Λ e * (∑ d ∈ (n / e).divisors, ((μ d : ℤ) : ℝ)) := by
  have hrhs : (∑ e ∈ n.divisors.filter (fun e => e ≤ v),
        Λ e * (∑ d ∈ (n / e).divisors, ((μ d : ℤ) : ℝ))) =
      ∑ e ∈ n.divisors.filter (fun e => e ≤ v),
        ∑ d ∈ (n / e).divisors, Λ e * ((μ d : ℤ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mul_sum]
  rw [hrhs]
  rw [← Finset.sum_sigma (s := n.divisors) (t := fun d => (n / d).divisors.filter (fun e => e ≤ v))
    (f := fun x => ((μ x.1 : ℤ) : ℝ) * Λ x.2)]
  rw [← Finset.sum_sigma (s := n.divisors.filter (fun e => e ≤ v)) (t := fun e => (n / e).divisors)
    (f := fun x => Λ x.1 * ((μ x.2 : ℤ) : ℝ))]
  apply Finset.sum_bij (i := fun x _ => ⟨x.2, x.1⟩)
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨hd, he⟩
    rcases Finset.mem_filter.mp he with ⟨hem, hev⟩
    have hdn : x.1 ∣ n := (Nat.mem_divisors.mp hd).1
    have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hd).2
    have hden : x.2 ∣ n / x.1 := (Nat.mem_divisors.mp hem).1
    have hen : x.2 ∣ n := dvd_trans hden (Nat.div_dvd_of_dvd hdn)
    rw [Finset.mem_sigma]
    constructor
    · rw [Finset.mem_filter]
      constructor
      · rw [Nat.mem_divisors]
        exact ⟨hen, hn0⟩
      · exact hev
    · rw [Nat.mem_divisors]
      constructor
      · have hden_mul : x.2 * x.1 ∣ n := by
          rcases hden with ⟨k, hk⟩
          refine ⟨k, ?_⟩
          rw [← Nat.mul_div_cancel' hdn, hk]
          ring
        exact (Nat.dvd_div_iff_mul_dvd hen).2 hden_mul
      · exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hen)
          (Nat.pos_of_dvd_of_pos hen (Nat.pos_of_ne_zero hn0)))
  · intro a ha b hb h
    cases a with
    | mk d₁ e₁ =>
      cases b with
      | mk d₂ e₂ =>
          apply Sigma.ext
          · exact congrArg Sigma.snd h
          · exact heq_of_eq (congrArg Sigma.fst h)
  · intro b hb
    rcases Finset.mem_sigma.mp hb with ⟨he, hd⟩
    rcases Finset.mem_filter.mp he with ⟨hem, hev⟩
    have hen : b.1 ∣ n := (Nat.mem_divisors.mp hem).1
    have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hem).2
    have hden : b.2 ∣ n / b.1 := (Nat.mem_divisors.mp hd).1
    have hdn : b.2 ∣ n := dvd_trans hden (Nat.div_dvd_of_dvd hen)
    refine ⟨⟨b.2, b.1⟩, ?_, rfl⟩
    rw [Finset.mem_sigma]
    constructor
    · rw [Nat.mem_divisors]
      exact ⟨hdn, hn0⟩
    · rw [Finset.mem_filter]
      constructor
      · rw [Nat.mem_divisors]
        constructor
        · have hden_mul : b.1 * b.2 ∣ n := by
            rcases hden with ⟨k, hk⟩
            refine ⟨k, ?_⟩
            rw [← Nat.mul_div_cancel' hen, hk]
            ring
          exact (Nat.dvd_div_iff_mul_dvd hdn).2 (by simpa [Nat.mul_comm] using hden_mul)
        · exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdn)
            (Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero hn0)))
      · exact hev
  · intro x hx
    rw [mul_comm]

/-- 完整第二层和: `Σ_{d|n} Σ_{e|n/d, e≤v} μ(d)Λ(e) = Λ(n)·[n ≤ v]`. -/
theorem vaughanFullSecondSum (n v : ℕ) :
    (∑ d ∈ n.divisors, ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v),
        ((μ d : ℤ) : ℝ) * Λ e) = if n ≤ v then Λ n else 0 := by
  rw [vaughanDoubleSum_swap]
  have hsum : (∑ e ∈ n.divisors.filter (fun e => e ≤ v),
        Λ e * (∑ d ∈ (n / e).divisors, ((μ d : ℤ) : ℝ))) =
      if n ≤ v then Λ n else 0 := by
    rw [Finset.sum_congr rfl (by
      intro e he
      rw [moebiusDivisorSum_eq_ite, mul_ite, mul_one, mul_zero])]
    rw [← Finset.sum_filter (s := n.divisors.filter (fun e => e ≤ v))
      (p := fun e => n / e = 1)]
    have hfilt : (n.divisors.filter (fun e => e ≤ v)).filter (fun e => n / e = 1) =
        n.divisors.filter (fun e => e = n ∧ n ≤ v) := by
      ext e
      by_cases hn0 : n = 0
      · subst n
        simp
      · simp only [Finset.mem_filter, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨⟨hed, hn0'⟩, hev⟩, hdiv⟩
          have heeq : e = n := (div_eq_one_iff_eq hed hn0').1 hdiv
          subst e
          simp [hn0', hev]
        · rintro ⟨⟨hed, hn0'⟩, ⟨heq, hnv⟩⟩
          subst e
          simp [hn0', hnv, Nat.div_self (Nat.pos_of_ne_zero hn0')]
    rw [hfilt]
    by_cases hnv : n ≤ v
    · rw [if_pos hnv]
      by_cases hn0 : n = 0
      · subst n
        simp
      · have hmem : n ∈ n.divisors.filter (fun e => e = n ∧ n ≤ v) := by
          rw [Finset.mem_filter, Nat.mem_divisors]
          exact ⟨⟨dvd_refl n, hn0⟩, ⟨rfl, hnv⟩⟩
        rw [Finset.sum_eq_single_of_mem n hmem]
        intro e he hen
        rw [Finset.mem_filter] at he
        exact False.elim (hen he.2.1)
    · rw [if_neg hnv]
      apply Finset.sum_eq_zero
      intro e he
      rw [Finset.mem_filter] at he
      exact False.elim (hnv he.2.2)
  exact hsum

/-- **Vaughan 恒等式** (经典三段形式): 对 `n > v`,

  `Λ n = vaughanFirst n u − vaughanMiddle n u v + vaughanThird n u v`.

这是 Bombieri--Vinogradov / 加权 Pan 均值定理 type I/II 分解实际消费的形式:
中间项经 `vaughanFullSecondSum` 与第二项互相抵消 (`n > v` 时
`Σ_{d|n} Σ_{e|n/d,e≤v} μ(d)Λ(e) = 0`). -/
theorem vaughanIdentity_threeTerm (n u v : ℕ) (hnv : v < n) :
    Λ n = vaughanFirst n u - vaughanMiddle n u v + vaughanThird n u v := by
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
  have hsecond : vaughanSecond n u v = -vaughanMiddle n u v := by
    unfold vaughanSecond vaughanMiddle
    have hfull : (∑ d ∈ n.divisors, ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v),
        ((μ d : ℤ) : ℝ) * Λ e) = 0 := by
      rw [vaughanFullSecondSum]
      rw [if_neg (not_le_of_gt hnv)]
    linarith
  rw [vaughanIdentity, hsecond]
  abel

end

end AnalyticNumberTheory.Sieve
