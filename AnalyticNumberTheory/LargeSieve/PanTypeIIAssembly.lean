import AnalyticNumberTheory.LargeSieve.PanTypeIAssembly
import AnalyticNumberTheory.Sieve.PanMeanValueBody

/-!
! # AnalyticNumberTheory.LargeSieve.PanTypeIIAssembly

## S2b-II: panTypeIICharSqSum 的原特征分解 (issue #43, type II)

对 type II 特征和 panTypeIIV3CharSum (vaughanThird 序列) 完全平行地实现
S2b 分解: t_q(m) ≤ 2·Σ_{q' | q} φ(q)·P2_{q'}(m) + 2·φ(q)·D2_q(m)².
证明装置与 PanTypeIAssembly.lean 的 S2b 完全相同 (逐点平方界 + 纤维大小),
仅序列换成 vaughanThird(n,u,v). 零 sorry, 零非形式化输入.
-/

namespace AnalyticNumberTheory.LargeSieve

open Finset
open scoped BigOperators
open Classical
open AnalyticNumberTheory.Sieve
open DirichletCharacter
open scoped ArithmeticFunction

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

/-! ### S2b-II: 原特征分解 (成真; 直接逐项上界 + 纤维大小) -/

/-- 原特征部分: P2_{q'}(m) = Σ_{χ' 原特征 mod q'} ‖V_χ'(m)‖². -/
noncomputable def panTypeIIPrimitiveSqSum (q' m u v : ℕ) : ℝ :=
  ∑ χ' ∈ (Finset.univ : Finset (DirichletCharacter ℂ q')).filter (fun χ' => χ'.IsPrimitive),
    ‖panTypeIIV3CharSum q' m u v χ'‖ ^ 2

/-- 非负: P2_{q'}(m) ≥ 0 (平方和). -/
lemma panTypeIIPrimitiveSqSum_nonneg (q' m u v : ℕ) : 0 ≤ panTypeIIPrimitiveSqSum q' m u v := by
  unfold panTypeIIPrimitiveSqSum
  exact Finset.sum_nonneg (fun χ' hχ' => sq_nonneg _)

/-- 非互素密度项: D2_q(m) = Σ_{n ≤ m, (n,q) > 1} |vaughanThird(n,u,v)|. -/
noncomputable def panTypeII_nonCoprimeDensity (q m u v : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (m + 1), if (n.gcd q) ≠ 1 then |vaughanThird n u v| else 0

/-- 非互素密度项非负. -/
lemma panTypeII_nonCoprimeDensity_nonneg (q m u v : ℕ) : 0 ≤ panTypeII_nonCoprimeDensity q m u v := by
  unfold panTypeII_nonCoprimeDensity
  exact Finset.sum_nonneg (fun n hn => by
    by_cases hc : (n.gcd q) ≠ 1 <;> simp [hc, abs_nonneg])

/-- **S2-II 关键点式界 (成真)**: ‖V_χ(m)‖ ≤ ‖V_{χ.primitiveCharacter}(m)‖ + D2_q(m). -/
lemma panTypeIIV3CharSum_norm_le_primitive {q m u v : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ‖panTypeIIV3CharSum q m u v χ‖ ≤
      ‖panTypeIIV3CharSum χ.conductor m u v χ.primitiveCharacter‖ +
        panTypeII_nonCoprimeDensity q m u v := by
  let ψ := χ.primitiveCharacter
  let S_not : ℂ :=
    ∑ n ∈ Finset.range (m + 1),
      if ¬ n.Coprime q then (vaughanThird n u v : ℂ) * ψ (n : ZMod χ.conductor) else 0
  have hdiff : panTypeIIV3CharSum q m u v χ - panTypeIIV3CharSum χ.conductor m u v ψ = -S_not := by
    unfold panTypeIIV3CharSum S_not ψ
    rw [← Finset.sum_sub_distrib]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : n.Coprime q
    · simp [hc, dirichletChar_eq_primitiveCharacter_of_coprime χ hc]
    · have hnu : ¬ IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).not.mpr hc
      have hz : χ (n : ZMod q) = 0 := MulChar.map_nonunit χ hnu
      simp [hc, hz]
  have hnorm1 : ‖panTypeIIV3CharSum q m u v χ‖ ≤
      ‖panTypeIIV3CharSum χ.conductor m u v ψ‖ + ‖S_not‖ := by
    calc
      ‖panTypeIIV3CharSum q m u v χ‖
          = ‖panTypeIIV3CharSum χ.conductor m u v ψ +
              (panTypeIIV3CharSum q m u v χ - panTypeIIV3CharSum χ.conductor m u v ψ)‖ := by
              congr 1
              abel
      _ ≤ ‖panTypeIIV3CharSum χ.conductor m u v ψ‖ +
            ‖panTypeIIV3CharSum q m u v χ - panTypeIIV3CharSum χ.conductor m u v ψ‖ := by
            exact norm_add_le _ _
      _ = ‖panTypeIIV3CharSum χ.conductor m u v ψ‖ + ‖S_not‖ := by
            rw [hdiff, norm_neg]
  have hnorm2 : ‖S_not‖ ≤ panTypeII_nonCoprimeDensity q m u v := by
    calc
      ‖S_not‖
          ≤ ∑ n ∈ Finset.range (m + 1),
              ‖(if ¬ n.Coprime q then (vaughanThird n u v : ℂ) * ψ (n : ZMod χ.conductor) else 0)‖ := by
              simpa [S_not] using
                (norm_sum_le (s := Finset.range (m + 1))
                  (f := fun n =>
                    (if ¬ n.Coprime q then (vaughanThird n u v : ℂ) * ψ (n : ZMod χ.conductor)
                     else 0)))
      _ = ∑ n ∈ Finset.range (m + 1),
              (if ¬ n.Coprime q then ‖(vaughanThird n u v : ℂ) * ψ (n : ZMod χ.conductor)‖ else 0) := by
              apply Finset.sum_congr rfl
              intro n hn
              by_cases hc : n.Coprime q <;> simp [hc]
      _ ≤ ∑ n ∈ Finset.range (m + 1), (if ¬ n.Coprime q then |vaughanThird n u v| else 0) := by
              apply Finset.sum_le_sum
              intro n hn
              by_cases hc : n.Coprime q
              · simp [hc]
              · have hle : ‖(vaughanThird n u v : ℂ) * ψ (n : ZMod χ.conductor)‖ ≤ |vaughanThird n u v| := by
                  calc
                    ‖(vaughanThird n u v : ℂ) * ψ (n : ZMod χ.conductor)‖
                        ≤ ‖(vaughanThird n u v : ℂ)‖ * ‖ψ (n : ZMod χ.conductor)‖ := norm_mul_le _ _
                    _ = |vaughanThird n u v| * ‖ψ (n : ZMod χ.conductor)‖ := by
                          congr 1
                          exact RCLike.norm_ofReal (vaughanThird n u v)
                    _ ≤ |vaughanThird n u v| * 1 := by
                          exact mul_le_mul_of_nonneg_left
                            (dirichletChar_norm_le_one χ.conductor ψ (n : ZMod χ.conductor))
                            (abs_nonneg _)
                    _ = |vaughanThird n u v| := by simp
                simpa [hc] using hle
      _ = panTypeII_nonCoprimeDensity q m u v := by
            unfold panTypeII_nonCoprimeDensity
            apply Finset.sum_congr rfl
            intro n hn
            by_cases hc : n.Coprime q <;> simp [hc, Nat.Coprime]
  simpa [ψ] using le_trans hnorm1 (add_le_add_right hnorm2 (‖panTypeIIV3CharSum χ.conductor m u v ψ‖))

/-- **S2-II 平方界**: ‖V_χ‖² ≤ 2‖V_{χ.prim}‖² + 2·D2_q(m)². -/
lemma panTypeIIV3CharSum_sq_le_primitive {q m u v : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ‖panTypeIIV3CharSum q m u v χ‖ ^ 2 ≤
      2 * ‖panTypeIIV3CharSum χ.conductor m u v χ.primitiveCharacter‖ ^ 2 +
        2 * (panTypeII_nonCoprimeDensity q m u v) ^ 2 := by
  let V := panTypeIIV3CharSum q m u v χ
  let W := panTypeIIV3CharSum χ.conductor m u v χ.primitiveCharacter
  let D := panTypeII_nonCoprimeDensity q m u v
  have hnorm : ‖V‖ ≤ ‖W‖ + D := by
    simpa [V, W, D] using (panTypeIIV3CharSum_norm_le_primitive (q := q) (m := m) (u := u) (v := v) χ)
  have hnonneg : 0 ≤ ‖W‖ + D := add_nonneg (norm_nonneg _) (panTypeII_nonCoprimeDensity_nonneg q m u v)
  have hs : ‖V‖ ^ 2 ≤ (‖W‖ + D) ^ 2 := by
    simpa [pow_two] using mul_le_mul hnorm hnorm (norm_nonneg _) hnonneg
  have hsq : (‖W‖ + D) ^ 2 ≤ 2 * ‖W‖ ^ 2 + 2 * D ^ 2 := by
    nlinarith [sq_nonneg (‖W‖ - D)]
  have hfin : ‖V‖ ^ 2 ≤ 2 * ‖W‖ ^ 2 + 2 * D ^ 2 := by
    calc
      ‖V‖ ^ 2 ≤ (‖W‖ + D) ^ 2 := hs
      _ ≤ 2 * ‖W‖ ^ 2 + 2 * D ^ 2 := hsq
  simpa [V, W, D] using hfin

/-- 纤维上界 (q' 层求和): 模 q 中 conductor = q' 的特征对原特征平方和的贡献
  ≤ φ(q)·P2_{q'}(m) (纤维大小 ≤ φ(q), 逐项 ‖V_{χ.prim}‖² ≤ P2_{q'}(m)). -/
lemma panTypeII_primitiveFiberSqSum_le {q q' m u v : ℕ} (hq : 0 < q) :
    (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor = q'),
      ‖panTypeIIV3CharSum q' m u v (panTypeI_liftPrimitive q' q χ)‖ ^ 2) ≤
    (Nat.totient q : ℝ) * panTypeIIPrimitiveSqSum q' m u v := by
  let s₁ : Finset (DirichletCharacter ℂ q) :=
    (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor = q')
  have hterm : ∀ χ ∈ s₁, ‖panTypeIIV3CharSum q' m u v (panTypeI_liftPrimitive q' q χ)‖ ^ 2 ≤
      panTypeIIPrimitiveSqSum q' m u v := by
    intro χ hχ
    have hχ' : χ.conductor = q' := (Finset.mem_filter.mp hχ).2
    rw [panTypeIIPrimitiveSqSum]
    exact Finset.single_le_sum (fun χ' hχ' => sq_nonneg ‖panTypeIIV3CharSum q' m u v χ'‖)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, panTypeI_liftPrimitive_isPrimitive χ hχ'⟩)
  have hsize : s₁.card ≤ Nat.totient q := by
    calc
      s₁.card ≤ (Finset.univ : Finset (DirichletCharacter ℂ q)).card := by
            exact Finset.card_le_card (Finset.filter_subset _ _)
      _ = Fintype.card (DirichletCharacter ℂ q) := Finset.card_univ
      _ = Nat.totient q := panTypeI_charCard_eq_totient q hq
  calc
    (∑ χ ∈ s₁, ‖panTypeIIV3CharSum q' m u v (panTypeI_liftPrimitive q' q χ)‖ ^ 2)
        ≤ ∑ χ ∈ s₁, panTypeIIPrimitiveSqSum q' m u v := by
          exact Finset.sum_le_sum (fun χ hχ => hterm χ hχ)
    _ = (s₁.card : ℝ) * panTypeIIPrimitiveSqSum q' m u v := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Nat.totient q : ℝ) * panTypeIIPrimitiveSqSum q' m u v := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsize) (panTypeIIPrimitiveSqSum_nonneg q' m u v)

/-- **S2b-II (成真)**: 全特征平方和的原特征分解 (朴素系数 φ(q)):
  t_q(m) ≤ 2·Σ_{q' | q} φ(q)·P2_{q'}(m) + 2·φ(q)·D2_q(m)².
  注: 与 type I 的 S2b 平行 (序列换成 vaughanThird); 精确系数 1 的注入版本
  同样受 conductor cast 限制, 留待装配重定形. -/
theorem panTypeII_sqSum_primitiveDecomposition (q m u v : ℕ) (hq : 0 < q) :
    panTypeIICharSqSum q m u v ≤
      2 * (∑ q' ∈ q.divisors, (Nat.totient q : ℝ) * panTypeIIPrimitiveSqSum q' m u v) +
        2 * (Nat.totient q : ℝ) * (panTypeII_nonCoprimeDensity q m u v) ^ 2 := by
  haveI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hpoint : ∀ χ : DirichletCharacter ℂ q,
      ‖panTypeIIV3CharSum q m u v χ‖ ^ 2 ≤
        2 * ‖panTypeIIV3CharSum χ.conductor m u v χ.primitiveCharacter‖ ^ 2 +
          2 * (panTypeII_nonCoprimeDensity q m u v) ^ 2 := by
    intro χ
    exact panTypeIIV3CharSum_sq_le_primitive (q := q) (m := m) (u := u) (v := v) χ
  have hcard : Fintype.card (DirichletCharacter ℂ q) = Nat.totient q := panTypeI_charCard_eq_totient q hq
  have h1 : panTypeIICharSqSum q m u v ≤
      2 * (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum χ.conductor m u v χ.primitiveCharacter‖ ^ 2) +
        2 * (Nat.totient q : ℝ) * (panTypeII_nonCoprimeDensity q m u v) ^ 2 := by
    unfold panTypeIICharSqSum
    calc
      (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum q m u v χ‖ ^ 2)
          ≤ ∑ χ : DirichletCharacter ℂ q,
              (2 * ‖panTypeIIV3CharSum χ.conductor m u v χ.primitiveCharacter‖ ^ 2 +
                2 * (panTypeII_nonCoprimeDensity q m u v) ^ 2) := by
              exact Finset.sum_le_sum (fun χ hχ => hpoint χ)
      _ = 2 * (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum χ.conductor m u v χ.primitiveCharacter‖ ^ 2) +
            2 * (Nat.totient q : ℝ) * (panTypeII_nonCoprimeDensity q m u v) ^ 2 := by
              rw [Finset.sum_add_distrib]
              rw [← Finset.mul_sum]
              rw [Finset.sum_const, nsmul_eq_mul]
              rw [Finset.card_univ]
              rw [hcard]
              ring
  have h2 : (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum χ.conductor m u v χ.primitiveCharacter‖ ^ 2) ≤
      ∑ q' ∈ q.divisors, (Nat.totient q : ℝ) * panTypeIIPrimitiveSqSum q' m u v := by
    calc
      (∑ χ : DirichletCharacter ℂ q, ‖panTypeIIV3CharSum χ.conductor m u v χ.primitiveCharacter‖ ^ 2)
          = ∑ χ : DirichletCharacter ℂ q,
              ∑ q' ∈ q.divisors, (if χ.conductor = q'
                  then ‖panTypeIIV3CharSum χ.conductor m u v χ.primitiveCharacter‖ ^ 2 else 0) := by
              apply Finset.sum_congr rfl
              intro χ hχ
              have hmem : χ.conductor ∈ q.divisors := by
                exact Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, Nat.ne_of_gt hq⟩
              rw [Finset.sum_ite_eq]
              simp [hmem]
      _ = ∑ q' ∈ q.divisors,
            ∑ χ : DirichletCharacter ℂ q, (if χ.conductor = q'
                then ‖panTypeIIV3CharSum χ.conductor m u v χ.primitiveCharacter‖ ^ 2 else 0) := by
            rw [Finset.sum_comm]
      _ = ∑ q' ∈ q.divisors,
            ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor = q'),
              ‖panTypeIIV3CharSum χ.conductor m u v χ.primitiveCharacter‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro q' hq'
            rw [← Finset.sum_filter]
      _ ≤ ∑ q' ∈ q.divisors, (Nat.totient q : ℝ) * panTypeIIPrimitiveSqSum q' m u v := by
            apply Finset.sum_le_sum
            intro q' hq'
            have hfiber_cast : (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor = q'),
                  ‖panTypeIIV3CharSum χ.conductor m u v χ.primitiveCharacter‖ ^ 2) =
                (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.conductor = q'),
                  ‖panTypeIIV3CharSum q' m u v (panTypeI_liftPrimitive q' q χ)‖ ^ 2) := by
              apply Finset.sum_congr rfl
              intro χ hχ
              have hχ' : χ.conductor = q' := (Finset.mem_filter.mp hχ).2
              cases hχ'
              simp [panTypeI_liftPrimitive]
            rw [hfiber_cast]
            exact panTypeII_primitiveFiberSqSum_le (q := q) (q' := q') (m := m) (u := u) (v := v) hq
  nlinarith [h1, h2]

end
