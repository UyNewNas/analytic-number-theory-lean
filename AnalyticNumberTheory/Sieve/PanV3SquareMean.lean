/-
! # AnalyticNumberTheory.Sieve.PanV3SquareMean

## type II 双线性片段 (vaughanThird) 的平方和界与逐 q 大筛归约 (线 T2i, ant #15)

本模块推进 `PanTypeIICharacterMeanValue` (见 `PanMeanValueBody.lean` §5/§5.2) 的
解析核心: 乘法大筛双线性特征均值界 `panTypeIICharMeanSieveBound` 的两个可证组件
(与 `PanV1SquareMean.lean` 对 type I 的处理完全同构):

1. **vaughanThird 平方和界** (纯初等/组合, 本模块完整证明):
   `Σ_{n ≤ N} vaughanThird(n,u,v)² ≤ N·(1+log(N+1))⁵`.
   路线: 点式界 `|vaughanThird(n,u,v)| ≤ τ(n)·log(n+1)` — 双线性结构的
   `Σ_{e|n/d, v<e} Λ(e) ≤ Σ_{e|n/d} Λ(e) = log(n/d)` 由 mathlib 的
   `ArithmeticFunction.vonMangoldt_sum` 给出 (Λ ≥ 0), 其余同 type I
   (τ(n) = n.divisors.card, `|μ(d)| ≤ 1`); 再证 τ² 的前 N 项和
   `Σ_{n≤N} τ(n)² ≤ N·(1+log(N+1))³` (双计数 + lcm 归约).

2. **逐 q 特征平方和的大筛归约** (点式, 本模块完整证明):
   `Σ_χ ‖V_χ(m)‖² ≤ (φ(q)/q)·largeSieveBound(m+1, 1/q²)·Σ_{n≤m} vaughanThird(n,u,v)²`
   其中 `V_χ(m) = Σ_{n≤m} vaughanThird(n,u,v)·χ(n)` (即 `panTypeIIV3CharSum`).
   由 `characterSieveModulus_le` (模 q 点式特征大筛) + `largeSieveRationalPoints`
   (有理点集加法大筛) 装配; 再把 max 归约 (`panTypeIICharSqrtMeanMaxY` ≤ 逐 y 求和)
   深化到 `panTypeIICharSqrtMeanMaxY_le_sieveSqrtSum`.

**红队注记 (装配边界)**: 求和到 `q ≤ Q` 的全体特征版本 (Bombieri--Davenport,
`panTypeIICharSquareMeanBound`) 需要原特征分解与 Gauss 和 (`|τ(χ)|² = q`),
保持为开放目标; 逐 q 点式版本把归约链推进到加法大筛常数 × vaughanThird 平方和,
即 `panTypeIICharSqrtMeanMaxY_le_sieveSqrtSum` 的 RHS 只剩初等对象
(筛常数、vaughanThird L²、外层 (y,a) 权重和). 所有断言零 sorry.
-/

import AnalyticNumberTheory.Sieve.PanMeanValueBody
import AnalyticNumberTheory.LargeSieve.Multiplicative
import AnalyticNumberTheory.Sieve.LcmWeightDivisorBounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

namespace AnalyticNumberTheory.Sieve

open Finset Real

open AnalyticNumberTheory.LargeSieve

open scoped Classical
open scoped ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-! ## 1. vaughanThird 的初等点式界 -/

/-- `μ(d) ∈ {-1, 0, 1}`: `|μ d| ≤ 1`. -/
lemma v3_moebius_abs_le_one (d : ℕ) : |((μ d : ℤ) : ℝ)| ≤ 1 := by
  by_cases h : Squarefree d
  · have hμ : (μ d : ℤ) = (-1 : ℤ) ^ ArithmeticFunction.cardFactors d := by
      unfold ArithmeticFunction.moebius
      simp [h]
    rw [hμ]
    have hpow : |(((-1 : ℤ) ^ ArithmeticFunction.cardFactors d : ℤ) : ℝ)| = 1 := by
      rw [← Int.cast_abs, abs_pow, abs_neg, abs_one]
      norm_num
    rw [hpow]
  · have hμ : (μ d : ℤ) = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree h
    rw [hμ]
    norm_num

/-- `vaughanThird 0 u v = 0` (`0.divisors` 中 `0 < d` 过滤为空). -/
lemma vaughanThird_zero (u v : ℕ) : vaughanThird 0 u v = 0 := by
  unfold vaughanThird
  simp [Nat.divisors_zero]

/-- vonMangoldt 非负 (mathlib `ArithmeticFunction.vonMangoldt_nonneg` 的别名). -/
lemma v3_vonMangoldt_nonneg (e : ℕ) : 0 ≤ Λ e :=
  ArithmeticFunction.vonMangoldt_nonneg

/-- **vaughanThird 点式界**: `|vaughanThird(n,u,v)| ≤ τ(n)·log(n+1)`,
  其中 `τ(n) = n.divisors.card`. 双线性结构: 内层
  `Σ_{e|n/d} Λ(e) = log(n/d)` (mathlib `vonMangoldt_sum`, Λ ≥ 0),
  外层 `|μ(d)| ≤ 1`. 对 n = 0 平凡 (`vaughanThird 0 u v = 0`). -/
lemma vaughanThird_abs_le (n u v : ℕ) :
    |vaughanThird n u v| ≤ (n.divisors.card : ℝ) * Real.log (n + 1) := by
  by_cases hn : n = 0
  · subst n
    simp [vaughanThird_zero]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let s : Finset ℕ := n.divisors.filter (fun d => u < d)
    let t : ℕ → Finset ℕ := fun d => (n / d).divisors.filter (fun e => v < e)
    have hterm : ∀ d ∈ s, (∑ e ∈ t d, |((μ d : ℤ) : ℝ) * Λ e|) ≤ Real.log (n + 1) := by
      intro d hd
      have hdmem : d ∈ n.divisors := (Finset.mem_filter.mp hd).1
      have hdn : d ∣ n := (Nat.mem_divisors.mp hdmem).1
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hnpos
      have hnd : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd hnpos hdn) hdpos
      have hlog_le : Real.log ((n / d : ℕ) : ℝ) ≤ Real.log (n + 1) := by
        apply Real.log_le_log
        · exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hnd)
        · exact_mod_cast (le_trans (Nat.div_le_self n d) (Nat.le_succ n))
      calc
        (∑ e ∈ t d, |((μ d : ℤ) : ℝ) * Λ e|)
            = ∑ e ∈ t d, (|((μ d : ℤ) : ℝ)| * Λ e) := by
              apply Finset.sum_congr rfl
              intro e he
              rw [abs_mul]
              rw [abs_of_nonneg (v3_vonMangoldt_nonneg e)]
        _ ≤ ∑ e ∈ t d, Λ e := by
              apply Finset.sum_le_sum
              intro e he
              exact mul_le_of_le_one_left (v3_vonMangoldt_nonneg e) (v3_moebius_abs_le_one d)
        _ ≤ ∑ e ∈ (n / d).divisors, Λ e := by
              exact Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.filter_subset (fun e => v < e) (n / d).divisors)
                (fun _ _ _ => v3_vonMangoldt_nonneg _)
        _ = Real.log ((n / d : ℕ) : ℝ) := by
              exact ArithmeticFunction.vonMangoldt_sum (n := n / d)
        _ ≤ Real.log (n + 1) := hlog_le
    calc
      |vaughanThird n u v| ≤ ∑ d ∈ s, |∑ e ∈ t d, ((μ d : ℤ) : ℝ) * Λ e| := by
            unfold vaughanThird s t
            exact Finset.abs_sum_le_sum_abs
              (fun d => ∑ e ∈ (n / d).divisors.filter (fun e => v < e), ((μ d : ℤ) : ℝ) * Λ e)
              (n.divisors.filter (fun d => u < d))
      _ ≤ ∑ d ∈ s, ∑ e ∈ t d, |((μ d : ℤ) : ℝ) * Λ e| := by
            apply Finset.sum_le_sum
            intro d hd
            exact Finset.abs_sum_le_sum_abs (fun e => ((μ d : ℤ) : ℝ) * Λ e) (t d)
      _ ≤ ∑ d ∈ s, Real.log (n + 1) := by
            exact Finset.sum_le_sum (fun d hd => hterm d hd)
      _ = (s.card : ℝ) * Real.log (n + 1) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n.divisors.card : ℝ) * Real.log (n + 1) := by
            have hc : s.card ≤ n.divisors.card :=
              Finset.card_le_card (Finset.filter_subset (fun d => u < d) n.divisors)
            have hlog : 0 ≤ Real.log (n + 1) := by
              have h1 : 1 ≤ n + 1 := by omega
              exact Real.log_nonneg (by exact_mod_cast h1)
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hlog

/-! ## 2–4. Shared LCM-weight compatibility wrappers -/

/-- Compatibility wrapper for the shared harmonic-sum bound. -/
lemma v3_harmonic_Icc_le (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M, (1 : ℝ) / (k : ℝ)) ≤ 1 + Real.log (M + 1) :=
  LcmWeightBounds.harmonic_Icc_le M

/-- Compatibility wrapper for the shared multiples-count identity. -/
lemma v3_card_multiples_Icc (N m : ℕ) (hm : 1 ≤ m) :
    ((Finset.Icc 1 N).filter (fun n => m ∣ n)).card = N / m :=
  LcmWeightBounds.card_multiples_Icc N m hm

/-- Compatibility wrapper for the shared reciprocal-LCM double-sum bound. -/
lemma v3_lcm_inv_sum_le (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 N,
      (1 : ℝ) / (Nat.lcm d e : ℝ)) ≤
      (1 + Real.log (N + 1)) ^ 3 :=
  LcmWeightBounds.lcm_inv_sum_le N

/-- Compatibility wrapper for the shared divisor-count-square prefix bound. -/
lemma v3_divisorCountSq_sum_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ 2)) ≤
      (N : ℝ) * (1 + Real.log (N + 1)) ^ 3 :=
  LcmWeightBounds.divisorCountSq_sum_le N

/-! ## 5. vaughanThird 平方和界 -/

/-- **vaughanThird 平方和界**: `Σ_{n≤N} vaughanThird(n,u,v)² ≤ N·(1+log(N+1))⁵`.
  纯初等: 点式界 |vaughanThird| ≤ τ·log 与 τ² 前 N 项和. -/
theorem vaughanThird_l2_sum_le (u v : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
    (∑ n ∈ Finset.range (N + 1), (vaughanThird n u v) ^ 2) ≤
      C * (N : ℝ) * (1 + Real.log (N + 1)) ^ 5 := by
  refine ⟨1, by norm_num, ?_⟩
  intro N
  calc
    (∑ n ∈ Finset.range (N + 1), (vaughanThird n u v) ^ 2)
    = (vaughanThird 0 u v) ^ 2 + ∑ n ∈ Finset.Icc 1 N, (vaughanThird n u v) ^ 2 := by
          rw [Finset.sum_range_succ']
          -- 右边的 0 项换到左边位置
          rw [add_comm ((vaughanThird 0 u v) ^ 2)]
          congr 1
          -- Σ_{k∈range N} f(k+1) = Σ_{n∈Icc 1 N} f n (双射 k+1)
          apply Finset.sum_bij (s := Finset.range N) (t := Finset.Icc 1 N)
            (f := fun k => (vaughanThird (k + 1) u v) ^ 2)
            (g := fun n => (vaughanThird n u v) ^ 2)
            (i := fun k _ => k + 1)
          · intro k hk
            rw [Finset.mem_Icc]
            have hk' : k < N := Finset.mem_range.mp hk
            constructor
            · exact Nat.succ_pos k
            · exact Nat.succ_le_of_lt hk'
          · intro k₁ hk₁ k₂ hk₂ h
            omega
          · intro n hn
            rw [Finset.mem_Icc] at hn
            refine ⟨n - 1, ?_, ?_⟩
            · rw [Finset.mem_range]
              omega
            · have hn1 : 1 ≤ n := hn.1
              omega
          · intro k hk
            rfl
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (vaughanThird n u v) ^ 2 := by
          simp [vaughanThird_zero]
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ 2 * (Real.log (n + 1)) ^ 2) := by
          apply Finset.sum_le_sum
          intro n hn
          have hnonneg : 0 ≤ (n.divisors.card : ℝ) * Real.log (n + 1) := by
            have hlog : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega))
            exact mul_nonneg (by exact_mod_cast Nat.zero_le _) hlog
          have h1 : (vaughanThird n u v) ^ 2 ≤ ((n.divisors.card : ℝ) * Real.log (n + 1)) ^ 2 := by
            exact sq_le_sq.mpr (by simpa [abs_of_nonneg hnonneg] using vaughanThird_abs_le n u v)
          calc
            (vaughanThird n u v) ^ 2 ≤ ((n.divisors.card : ℝ) * Real.log (n + 1)) ^ 2 := h1
            _ = (n.divisors.card : ℝ) ^ 2 * (Real.log (n + 1)) ^ 2 := by ring
    _ ≤ (Real.log (N + 1)) ^ 2 * (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℝ) ^ 2)) := by
          -- log(n+1) ≤ log(N+1), 提出常数
          have hlog : ∀ n ∈ Finset.Icc 1 N, Real.log (n + 1) ≤ Real.log (N + 1) := by
            intro n hn
            apply Real.log_le_log
            · exact_mod_cast (Nat.succ_pos n)
            · exact_mod_cast (Nat.succ_le_succ (Finset.mem_Icc.mp hn).2)
          calc
            (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 * (Real.log (n + 1)) ^ 2)
                ≤ ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 * (Real.log (N + 1)) ^ 2 := by
                    apply Finset.sum_le_sum
                    intro n hn
                    exact mul_le_mul_of_nonneg_left
                      (sq_le_sq.mpr (by
                        have h1 : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega))
                        have h2 : 0 ≤ Real.log (N + 1) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 1 by omega))
                        simpa [abs_of_nonneg h1, abs_of_nonneg h2] using hlog n hn))
                      (sq_nonneg _)
            _ = (Real.log (N + 1)) ^ 2 * (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2) := by
                  rw [← Finset.sum_mul (s := Finset.Icc 1 N)
                    (f := fun n => (n.divisors.card : ℝ) ^ 2)
                    (a := (Real.log (N + 1)) ^ 2)]
                  ring
    _ ≤ (Real.log (N + 1)) ^ 2 * ((N : ℝ) * (1 + Real.log (N + 1)) ^ 3) := by
          exact mul_le_mul_of_nonneg_left (v3_divisorCountSq_sum_le N) (sq_nonneg _)
    _ = (Real.log (N + 1)) ^ 2 * (N : ℝ) * (1 + Real.log (N + 1)) ^ 3 := by ring
    _ ≤ 1 * (N : ℝ) * (1 + Real.log (N + 1)) ^ 5 := by
          have hlog : 0 ≤ Real.log (N + 1) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 1 by omega))
          have hle1 : (Real.log (N + 1)) ^ 2 ≤ (1 + Real.log (N + 1)) ^ 2 := by
            exact sq_le_sq.mpr (by
              have h1 : Real.log (N + 1) ≤ 1 + Real.log (N + 1) := by linarith
              simpa [abs_of_nonneg hlog, abs_of_nonneg (by linarith : 0 ≤ 1 + Real.log (N + 1))] using h1)
          have hle2 : (1 + Real.log (N + 1)) ^ 3 ≤ (1 + Real.log (N + 1)) ^ 5 := by
            have hc : 1 ≤ 1 + Real.log (N + 1) := by linarith
            have hcpos : 0 ≤ 1 + Real.log (N + 1) := by linarith
            calc
              (1 + Real.log (N + 1)) ^ 3 = (1 + Real.log (N + 1)) ^ 3 * 1 := by ring
              _ ≤ (1 + Real.log (N + 1)) ^ 3 * (1 + Real.log (N + 1)) ^ 2 := by
                    exact mul_le_mul_of_nonneg_left
                      (by simpa using (pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hc 2))
                      (pow_nonneg hcpos 3)
              _ = (1 + Real.log (N + 1)) ^ 5 := by ring
          have hN : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
          calc
            (Real.log (N + 1)) ^ 2 * (N : ℝ) * (1 + Real.log (N + 1)) ^ 3
                = (Real.log (N + 1)) ^ 2 * ((N : ℝ) * (1 + Real.log (N + 1)) ^ 3) := by ring
            _ ≤ (1 + Real.log (N + 1)) ^ 2 * ((N : ℝ) * (1 + Real.log (N + 1)) ^ 3) := by
                  exact mul_le_mul_of_nonneg_right hle1 (mul_nonneg hN (pow_nonneg (by linarith) 3))
            _ = (N : ℝ) * ((1 + Real.log (N + 1)) ^ 2 * (1 + Real.log (N + 1)) ^ 3) := by ring
            _ ≤ (N : ℝ) * (1 + Real.log (N + 1)) ^ 5 := by
                  have hpow : (1 + Real.log (N + 1)) ^ 2 * (1 + Real.log (N + 1)) ^ 3 =
                      (1 + Real.log (N + 1)) ^ 5 := by ring
                  rw [← hpow]
            _ ≤ 1 * (N : ℝ) * (1 + Real.log (N + 1)) ^ 5 := by simp

/-! ## 6. 逐 q 特征平方和的大筛归约 (点式) -/

/-- ℕ 求和 (range) 到 ℤ-Icc 求和的换序 (双射 n ↦ n). -/
private lemma sum_range_to_Icc_int {m : ℕ} {β : Type*} [AddCommMonoid β] (f : ℕ → β)
    (g : ℤ → β) (hfg : ∀ n : ℕ, f n = g (n : ℤ)) :
    (∑ n ∈ Finset.range (m + 1), f n) = ∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), g n := by
  rw [Finset.sum_bij (s := Finset.range (m + 1)) (t := Finset.Icc (0 : ℤ) (m : ℤ))
    (f := f) (g := g) (i := fun n _ => (n : ℤ))]
  · intro n hn
    rw [Finset.mem_Icc]
    have hn' : n < m + 1 := Finset.mem_range.mp hn
    constructor <;> omega
  · intro n₁ hn₁ n₂ hn₂ h
    exact_mod_cast h
  · intro z hz
    rw [Finset.mem_Icc] at hz
    refine ⟨z.toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · exact Int.toNat_of_nonneg hz.1
  · intro n hn
    exact hfg n

/-- **逐 q 特征平方和的大筛归约 (点式)**: 对每个模 q ≥ 1,
  `Σ_χ ‖V_χ(m)‖² ≤ (φ(q)/q)·largeSieveBound(m+1, 1/q²)·Σ_{n≤m} vaughanThird(n,u,v)²`.
  由 `characterSieveModulus_le` (模 q 点式特征大筛) + `largeSieveRationalPoints`
  (有理点集加法大筛) 装配; 这是乘法大筛均值 (`panTypeIICharSquareMeanBound`,
  求和到 q ≤ Q) 的逐 q 版本 — q-求和需要原特征与 Gauss 和, 保持开放. -/
theorem panTypeIICharSqSum_le_additiveSieve (q m u v : ℕ) (hq : 0 < q) :
    panTypeIICharSqSum q m u v ≤
      ((q.totient : ℝ) / (q : ℝ)) *
        largeSieveBound (m + 1) (1 / (q : ℝ) ^ 2) *
          (∑ n ∈ Finset.range (m + 1), (vaughanThird n u v) ^ 2) := by
  haveI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  let a : ℤ → ℂ := fun n => if 0 ≤ n then (vaughanThird n.toNat u v : ℂ) else 0
  let M : ℤ := -1
  let N : ℕ := m + 1
  -- Icc (M+1) (M+N) = Icc 0 (m:ℤ)
  have hIcc : Finset.Icc (M + 1) (M + N) = Finset.Icc (0 : ℤ) (m : ℤ) := by
    dsimp [M, N]
    have h2 : (-1 : ℤ) + ((m : ℤ) + 1) = (m : ℤ) := by omega
    rw [h2]
  -- 系数恒等: a (n : ℤ) = vaughanThird n u v
  have ha : ∀ n : ℕ, a (n : ℤ) = (vaughanThird n u v : ℂ) := by
    intro n
    have htn : (n : ℤ).toNat = n := by
      have hz : ((n : ℤ).toNat : ℤ) = (n : ℤ) := Int.toNat_of_nonneg (by omega)
      exact_mod_cast hz
    simp [a, htn]
  -- 特征和: Σ_{Icc} a n·χ(n) = panTypeIIV3CharSum q m u v χ
  have hchar : ∀ χ : DirichletCharacter ℂ q,
      (∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), a n * χ (n : ZMod q)) =
        panTypeIIV3CharSum q m u v χ := by
    intro χ
    unfold panTypeIIV3CharSum
    rw [← sum_range_to_Icc_int (f := fun n => (vaughanThird n u v : ℂ) * χ (n : ZMod q))
      (g := fun n => a n * χ (n : ZMod q))]
    · intro n
      simp [ha n]
  -- charReal 和: Σ_{Icc} charReal(n·r/q)·a n = Σ_{range} charReal·vaughanThird
  have hcr : ∀ r : ℕ,
      (∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ),
        (charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ))) : ℂ) * a n) =
      ∑ n ∈ Finset.range (m + 1),
        (charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ))) : ℂ) * (vaughanThird n u v : ℂ) := by
    intro r
    rw [← sum_range_to_Icc_int
      (f := fun n => (charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ))) : ℂ) * (vaughanThird n u v : ℂ))
      (g := fun n => (charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ))) : ℂ) * a n)]
    · intro n
      simp [ha n]
  -- characterSieveModulus_le (M = -1, N = m+1)
  have hcs := characterSieveModulus_le (q := q) a M N
  -- 左边: Σ_χ‖panTypeIIV3‖² = Σ_χ‖Σ_{Icc (M+1)(M+N)}‖²
  have hcsL : (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q m u v χ‖ ^ 2) =
      (∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * χ (n : ZMod q)‖ ^ 2) := by
    rw [hIcc]
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [(hchar χ).symm]
  -- 有理点集子集: {r/q : r < q} ⊆ rationalPoints q
  have hsubset : (Finset.range q).image (fun r : ℕ => (r : ℝ) / (q : ℝ)) ⊆ rationalPoints q := by
    intro x hx
    unfold rationalPoints
    rw [Finset.mem_biUnion]
    rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
    refine ⟨q, Finset.mem_Icc.mpr ⟨hq, le_rfl⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨r, hr, rfl⟩
  -- 加法大筛
  have hls := largeSieveRationalPoints M N q hq a
  -- 逐 r 的 RHS ≤ 有理点集上的和 (去重后)
  have hRstep : (∑ r ∈ Finset.range q,
        ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
          (charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ))) : ℂ) * a n‖ ^ 2)
      ≤ (∑ x ∈ rationalPoints q,
        ‖∑ n ∈ Finset.Icc (M + 1) (M + N), (charReal ((n : ℝ) * x) : ℂ) * a n‖ ^ 2) := by
    rw [hIcc]
    have hinj : Set.InjOn (fun r : ℕ => (r : ℝ) / (q : ℝ)) ↑(Finset.range q) := by
      intro r₁ hr₁ r₂ hr₂ h
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
      have hnum : (r₁ : ℝ) = (r₂ : ℝ) := by
        have : (r₁ : ℝ) / (q : ℝ) = (r₂ : ℝ) / (q : ℝ) := h
        field_simp [hq0] at this
        exact this
      exact_mod_cast hnum
    calc
      (∑ r ∈ Finset.range q, ‖∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ),
          (charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ))) : ℂ) * a n‖ ^ 2)
      = ∑ x ∈ (Finset.range q).image (fun r : ℕ => (r : ℝ) / (q : ℝ)),
          ‖∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), (charReal ((n : ℝ) * x) : ℂ) * a n‖ ^ 2 := by
          rw [Finset.sum_image]
          exact hinj
      _ ≤ ∑ x ∈ rationalPoints q,
          ‖∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), (charReal ((n : ℝ) * x) : ℂ) * a n‖ ^ 2 := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => sq_nonneg _)
  -- L² 范数和
  have hL2 : (∑ n ∈ Finset.Icc (0 : ℤ) (m : ℤ), ‖a n‖ ^ 2) =
      (∑ n ∈ Finset.range (m + 1), (vaughanThird n u v) ^ 2) := by
    rw [← sum_range_to_Icc_int (f := fun n => ‖(vaughanThird n u v : ℂ)‖ ^ 2)
      (g := fun n => ‖a n‖ ^ 2)]
    · apply Finset.sum_congr rfl
      intro n hn
      simp [sq_abs]
    · intro n
      simp [ha n]
  -- 主装配
  have hqφ : 0 < (q : ℝ) / (q.totient : ℝ) := by
    have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    have hφR : 0 < (q.totient : ℝ) := by exact_mod_cast (Nat.totient_pos.mpr hq)
    exact div_pos hqR hφR
  have hmain : (q : ℝ) / (q.totient : ℝ) * panTypeIICharSqSum q m u v ≤
      largeSieveBound (m + 1) (1 / (q : ℝ) ^ 2) *
        (∑ n ∈ Finset.range (m + 1), (vaughanThird n u v) ^ 2) := by
    calc
      (q : ℝ) / (q.totient : ℝ) * panTypeIICharSqSum q m u v
      = ((q : ℝ) / (q.totient : ℝ)) *
          (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q m u v χ‖ ^ 2) := by
            rfl
      _ = ((q : ℝ) / (q.totient : ℝ)) * (∑ χ : DirichletCharacter ℂ q,
            ‖∑ n ∈ Finset.Icc (M + 1) (M + N), a n * χ (n : ZMod q)‖ ^ 2) := by
            rw [hcsL]
      _ ≤ (∑ r ∈ Finset.range q,
            ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
              (charReal ((n : ℝ) * ((r : ℝ) / (q : ℝ))) : ℂ) * a n‖ ^ 2) := by
            simpa [mul_div_assoc] using hcs
      _ ≤ (∑ x ∈ rationalPoints q,
            ‖∑ n ∈ Finset.Icc (M + 1) (M + N), (charReal ((n : ℝ) * x) : ℂ) * a n‖ ^ 2) := hRstep
      _ ≤ largeSieveBound (m + 1) (1 / (q : ℝ) ^ 2) *
            (∑ n ∈ Finset.Icc (M + 1) (M + N), ‖a n‖ ^ 2) := hls
      _ = largeSieveBound (m + 1) (1 / (q : ℝ) ^ 2) *
            (∑ n ∈ Finset.range (m + 1), (vaughanThird n u v) ^ 2) := by
            rw [hIcc, hL2]
  -- 除以 (q/φ): S ≤ (φ/q)·T
  calc
    panTypeIICharSqSum q m u v
        ≤ largeSieveBound (m + 1) (1 / (q : ℝ) ^ 2) *
            (∑ n ∈ Finset.range (m + 1), (vaughanThird n u v) ^ 2) /
              ((q : ℝ) / (q.totient : ℝ)) := by
          exact (le_div_iff₀ hqφ).mpr (by simpa [mul_comm] using hmain)
    _ = ((q.totient : ℝ) / (q : ℝ)) *
          largeSieveBound (m + 1) (1 / (q : ℝ) ^ 2) *
          (∑ n ∈ Finset.range (m + 1), (vaughanThird n u v) ^ 2) := by
          field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hq),
            show (q.totient : ℝ) ≠ 0 by exact_mod_cast (Nat.totient_pos.mpr hq).ne']

/-! ## 7. max 归约: panTypeIICharSqrtMeanMaxY ≤ 逐 y 求和 -/

/-- `panTypeIICharSqrtMean` 非负 (|f(a)|, |log|, sqrt 均非负). -/
private lemma panTypeIICharSqrtMean_nonneg (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    0 ≤ panTypeIICharSqrtMean y X q f u v := by
  unfold panTypeIICharSqrtMean
  exact Finset.sum_nonneg (fun a ha =>
    mul_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.sqrt_nonneg _))

/-- **max 归约**: `panTypeIICharSqrtMeanMaxY ≤ Σ_{y ≤ x} panTypeIICharSqrtMean y`
  (max ≤ 非负项求和, 装配期去 max 用). -/
theorem panTypeIICharSqrtMeanMaxY_le_sum (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    panTypeIICharSqrtMeanMaxY X q x f u v ≤
      ∑ y ∈ Finset.range (x + 1), panTypeIICharSqrtMean y X q f u v := by
  unfold panTypeIICharSqrtMeanMaxY
  apply Finset.max'_le
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
  exact Finset.single_le_sum (fun y' hy' => panTypeIICharSqrtMean_nonneg y' X q f u v) hy

/-! ## 8. 深化归约: 特征平方和 → 加法大筛常数 × vaughanThird 平方和 -/

/-- **深化归约**: 逐 q 的 `panTypeIICharSqrtMeanMaxY` 被完全初等的
  加法大筛常数 × vaughanThird 平方和对象一致控制 (max 已去除):
  对每个 y ≤ x, a ≤ X, `√(Σ_χ‖V_χ(y/a)‖²)` ≤
  `√((φ(q)/q)·largeSieveBound(y/a+1, 1/q²))·√(Σ_{n≤y/a} vaughanThird(n,u,v)²)`.
  这是乘法大筛均值 (q-求和, 需 Gauss 和) 的逐 q 深化: RHS 只剩初等对象. -/
theorem panTypeIICharSqrtMeanMaxY_le_sieveSqrtSum (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) (hq : 0 < q) :
    panTypeIICharSqrtMeanMaxY X q x f u v ≤
      ∑ y ∈ Finset.range (x + 1), ∑ a ∈ Finset.Icc 1 X,
        |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          Real.sqrt (((q.totient : ℝ) / (q : ℝ)) *
            largeSieveBound (y / a + 1) (1 / (q : ℝ) ^ 2)) *
          Real.sqrt (∑ n ∈ Finset.range (y / a + 1), (vaughanThird n u v) ^ 2) := by
  calc
    panTypeIICharSqrtMeanMaxY X q x f u v
        ≤ ∑ y ∈ Finset.range (x + 1), panTypeIICharSqrtMean y X q f u v :=
          panTypeIICharSqrtMeanMaxY_le_sum X q x f u v
    _ = ∑ y ∈ Finset.range (x + 1), ∑ a ∈ Finset.Icc 1 X,
        |f a| / |Real.log ((y / a : ℕ) : ℝ)| * Real.sqrt (panTypeIICharSqSum q (y / a) u v) := by
          rfl
    _ ≤ ∑ y ∈ Finset.range (x + 1), ∑ a ∈ Finset.Icc 1 X,
        |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          Real.sqrt (((q.totient : ℝ) / (q : ℝ)) *
            largeSieveBound (y / a + 1) (1 / (q : ℝ) ^ 2) *
            (∑ n ∈ Finset.range (y / a + 1), (vaughanThird n u v) ^ 2)) := by
          apply Finset.sum_le_sum
          intro y hy
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt (panTypeIICharSqSum_le_additiveSieve q (y / a) u v hq))
            (div_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ ∑ y ∈ Finset.range (x + 1), ∑ a ∈ Finset.Icc 1 X,
        |f a| / |Real.log ((y / a : ℕ) : ℝ)| *
          Real.sqrt (((q.totient : ℝ) / (q : ℝ)) *
            largeSieveBound (y / a + 1) (1 / (q : ℝ) ^ 2)) *
          Real.sqrt (∑ n ∈ Finset.range (y / a + 1), (vaughanThird n u v) ^ 2) := by
          apply Finset.sum_le_sum
          intro y hy
          apply Finset.sum_le_sum
          intro a ha
          have hAB : 0 ≤ ((q.totient : ℝ) / (q : ℝ)) *
              largeSieveBound (y / a + 1) (1 / (q : ℝ) ^ 2) := by
            have h1 : 0 ≤ (q.totient : ℝ) / (q : ℝ) := by positivity
            have h2 : 0 ≤ largeSieveBound (y / a + 1) (1 / (q : ℝ) ^ 2) := by
              exact largeSieveBound_nonneg (y / a + 1) (by positivity)
            exact mul_nonneg h1 h2
          rw [Real.sqrt_mul hAB (∑ n ∈ Finset.range (y / a + 1), (vaughanThird n u v) ^ 2)]
          simp [mul_assoc]

end

end AnalyticNumberTheory.Sieve
