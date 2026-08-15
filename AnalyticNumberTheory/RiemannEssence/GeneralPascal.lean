import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-!
# RH 塔程序——Pascal 恒等式一般 d（Δ_{d+1,n} = t²·T_{d,n}，58-top-link (ii)）

J^{k,n}(t) = Σ_{i=0}^{k} C(k,i) · γ(n+i) · t^i
T_{d,n}(t) = J^{d,n+1}(t)² − J^{d,n}(t)·J^{d,n+2}(t)
Δ_{d+1,n}(t) = J^{d+1,n}(t)² − J^{d,n}(t)·J^{d+2,n}(t)

定理（一般 d，多项式恒等式）：Δ_{d+1,n} = t²·T_{d,n}。

证明结构（二项式递归）：
  1. J^{k+1,n} = J^{k,n} + t·J^{k,n+1}（J_rec，系数逐项 + choose_succ_succ'）；
  2. 记 A = J^{d,n}，B = J^{d,n+1}，C = J^{d,n+2}，则
     Δ_{d+1,n} = (A + tB)² − A·(A + 2tB + t²C) = t²·(B² − AC)（纯 ring）。

这统一了 PascalIdentity / 2 / 3 / 4 的逐 d ring 证明（d=1..4 各自展开即此定理的特例）。
-/

namespace RiemannEssence

open Polynomial

-- J^{k,n}(t) = Σ_{i=0}^{k} C(k,i) · γ(n+i) · t^i（ℝ[t] 中）
noncomputable def J (g : ℕ → ℝ) (k n : ℕ) : Polynomial ℝ :=
  ∑ i in Finset.range (k + 1),
    Polynomial.C ((Nat.choose k i : ℝ) * g (n + i)) * Polynomial.X ^ i

-- coeff 与 Finset 求和可交换
lemma coeff_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) (m : ℕ) :
    (∑ i in s, f i).coeff m = ∑ i in s, (f i).coeff m := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert, ih, Polynomial.coeff_add]

-- 系数：coeff (J g k n) m = if m < k+1 then C(k,m)·γ(n+m) else 0
lemma coeff_J (g : ℕ → ℝ) (k n m : ℕ) :
    (J g k n).coeff m = if m < k + 1 then (Nat.choose k m : ℝ) * g (n + m) else 0 := by
  unfold J
  rw [coeff_finset_sum]
  simp [Polynomial.coeff_C_mul_X_pow]

-- 二项式递归：J^{k+1,n} = J^{k,n} + X·J^{k,n+1}
lemma J_rec (g : ℕ → ℝ) (k n : ℕ) :
    J g (k + 1) n = J g k n + Polynomial.X * J g k (n + 1) := by
  ext m
  cases m with
  | zero =>
      have hg1 : 0 < k + 1 := by omega
      have hg2 : 0 < (k + 1) + 1 := by omega
      simp [coeff_J, Nat.choose_zero_right, Polynomial.coeff_X_mul_zero, hg1, hg2]
  | succ j =>
      have hx : (Polynomial.X * J g k (n + 1)).coeff (j + 1) = (J g k (n + 1)).coeff j := by
        rw [mul_comm, Polynomial.coeff_mul_X]
      rw [hx]
      simp only [coeff_J]
      by_cases hjk : j < k
      · have h1 : j + 1 < k + 1 := by omega
        have h2 : j + 1 < (k + 1) + 1 := by omega
        have h3 : j < k + 1 := by omega
        have h4 : (n + 1) + j = n + (j + 1) := by omega
        rw [if_pos h2, if_pos h1, if_pos h3, h4]
        have hch := Nat.choose_succ_succ' k j
        have hch' : ((Nat.choose (k + 1) (j + 1) : ℝ)) =
            (Nat.choose k j : ℝ) + (Nat.choose k (j + 1) : ℝ) := by
          exact_mod_cast hch
        rw [hch']
        ring
      · by_cases hjk2 : j = k
        · subst j
          have h1 : ¬ k + 1 < k + 1 := by omega
          have h2 : k + 1 < (k + 1) + 1 := by omega
          have h3 : k < k + 1 := by omega
          rw [if_neg h1, if_pos h2, if_pos h3]
          simp [Nat.choose_self]
          congr 1
          omega
        · have hgk : k < j := by omega
          have h1 : ¬ j + 1 < k + 1 := by omega
          have h2 : ¬ j + 1 < (k + 1) + 1 := by omega
          have h3 : ¬ j < k + 1 := by omega
          rw [if_neg h2, if_neg h1, if_neg h3]
          ring

-- 一般 d：Δ_{d+1,n} = X²·T_{d,n}（ℝ[X] 中的多项式恒等式）
lemma pascal_general (g : ℕ → ℝ) (d n : ℕ) :
    J g (d + 1) n ^ 2 - J g d n * J g (d + 2) n =
      Polynomial.X ^ 2 * (J g d (n + 1) ^ 2 - J g d n * J g d (n + 2)) := by
  rw [J_rec g d n]
  rw [J_rec g (d + 1) n, J_rec g d n, J_rec g d (n + 1)]
  ring

-- 点值形式：对一切 t，Δ_{d+1,n}(t) = t²·T_{d,n}(t)
lemma pascal_general_eval (g : ℕ → ℝ) (d n : ℕ) (t : ℝ) :
    (J g (d + 1) n).eval t ^ 2 - (J g d n).eval t * (J g (d + 2) n).eval t =
      t ^ 2 * ((J g d (n + 1)).eval t ^ 2 - (J g d n).eval t * (J g d (n + 2)).eval t) := by
  have h := pascal_general g d n
  apply_fun (fun p : Polynomial ℝ => p.eval t) at h
  simpa [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_sub] using h

end RiemannEssence
