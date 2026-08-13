/-
! # AnalyticNumberTheory.LargeSieve.Additive

## 加法大筛 (Additive large sieve; Montgomery 1971)

对 `δ`-well-spaced 的模 1 点集 `{x_r}` 与任意有限支撑复数序列 `a_n`,

  Σ_r |Σ_{M<n≤M+N} a_n e(n x_r)|² ≤ (N + 1/δ) · Σ_{M<n≤M+N} |a_n|²,

其中 `e(x) = exp(2πix)`. 这是 Bombieri--Vinogradov 定理与加权 Pan 均值定理
(`PanMeanValueUniform`) 证明的最底层解析输入; 乘法大筛与算术大筛都是它的
推论 (见图谱供给线 LS1 → LS2 → LS3)。

本模块完成三层工作:

1. **表示**: `AddCircle 1` 上的标准加法特征 `unitChar x = exp(2πix)`
   (mathlib 的 `AddCircle.toCircle`), 区间指数和 `circleCharSum`, 以及
   `wellSpaced` (模 1 距离下的 δ-分离)。
2. **目标陈述**: `MontgomeryLargeSievePrimal` / `MontgomeryLargeSieveDual`
   按仓库惯例写成带量词的 `Prop` 目标 (研究级开放核心, 不声称已证明)。
3. **对偶引理** (本模块已证明的机器): 对任意有限矩阵 `A` 与常数 `C ≥ 0`,
   原形式 (对任意 `a`) 与对偶形式 (对任意 `b`) 等价
   (`largeSieveDuality`)。这是大筛法证明的代数骨架: Montgomery 原证明先从
   对偶形式出发 (几何级数界 + Schur 检验), 对偶引理保证两种形式的常数一致。
   对偶形式按共轭转置定义 (`star (A i j)`); 经典表述中的 `e(nx)` 形式可由
   `b ↦ conj b` 与 `n ↦ -n` 的替换等价导出。

参考:
  - Montgomery, H.L. (1971), "Topics in Multiplicative Number Theory"
  - Iwaniec & Kowalski, "Analytic Number Theory" (2004), Ch. 7
  - Halberstam & Richert, "Sieve Methods" (1974), Ch. 9-10
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Tactic

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators

noncomputable section

/-! ## 1. 模 1 圆上的加法特征与指数和 -/

/-- `e(x) = exp(2πix)`: 模 1 圆 `AddCircle 1` 上的标准加法特征
(mathlib `AddCircle.toCircle`, 见 `AddCircle.toCircle_apply_mk`). -/
def unitChar (x : AddCircle (1 : ℝ)) : Circle :=
  AddCircle.toCircle (T := (1 : ℝ)) x

/-- `e(nx) = e(x)^n` (`n : ℤ`): 特征与整数系数的相容性
(`AddCircle.toCircle_zsmul`). -/
def charPow (n : ℤ) (x : AddCircle (1 : ℝ)) : Circle :=
  unitChar (n • x)

/-- 区间 `(M, M+N]` 上的加权指数和 `Σ_{M<n≤M+N} a_n e(nx)`. -/
noncomputable def circleCharSum (M : ℤ) (N : ℕ) (a : ℤ → ℂ) (x : AddCircle (1 : ℝ)) : ℂ :=
  ∑ n ∈ Finset.Icc (M + 1) (M + N), a n * (charPow n x : ℂ)

/-- `X ⊆ AddCircle 1` 是 `δ`-well-spaced 的: 任意两点的模 1 距离至少为 `δ`. -/
noncomputable def wellSpaced (X : Finset (AddCircle (1 : ℝ))) (δ : ℝ) : Prop :=
  ∀ ⦃x : AddCircle (1 : ℝ)⦄, x ∈ X → ∀ ⦃y : AddCircle (1 : ℝ)⦄, y ∈ X → x ≠ y → δ ≤ dist x y

/-! ## 2. 加法大筛目标陈述 -/

/-- **加法大筛** (Montgomery, 原形式): 对 `δ`-well-spaced 点集 `X` 与任意
有限支撑复数序列 `a : ℤ → ℂ`,

  Σ_{x∈X} |Σ_{M<n≤M+N} a_n e(nx)|² ≤ (N + 1/δ) · Σ_{M<n≤M+N} |a_n|².

研究级开放目标; 经典证明: 对偶形式 + 几何级数界 + Schur 检验. -/
def MontgomeryLargeSievePrimal (M : ℤ) (N : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ X : Finset (AddCircle (1 : ℝ)), wellSpaced X δ →
    ∀ a : ℤ → ℂ,
      ∑ x ∈ X, ‖circleCharSum M N a x‖ ^ 2 ≤
        ((N : ℝ) + 1 / δ) * ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖a n‖ ^ 2

/-- **加法大筛的对偶形式** (按共轭转置定义):

  Σ_{M<n≤M+N} |Σ_{x∈X} conj(e(nx))·b_x|² ≤ (N + 1/δ) · Σ_{x∈X} |b_x|².

经典表述把 `conj(e(nx))` 写成 `e(-nx)`, 由替换 `b ↦ conj b` 等价. -/
def MontgomeryLargeSieveDual (M : ℤ) (N : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ X : Finset (AddCircle (1 : ℝ)), wellSpaced X δ →
    ∀ b : AddCircle (1 : ℝ) → ℂ,
      ∑ n ∈ Finset.Icc (M + 1) (M + N),
        ‖∑ x ∈ X, star (charPow n x : ℂ) * b x‖ ^ 2 ≤
        ((N : ℝ) + 1 / δ) * ∑ x ∈ X, ‖b x‖ ^ 2

/-! ## 3. 对偶引理 (大筛法证明的代数骨架) -/

/-- **实数 Cauchy--Schwarz** (Finset): `(Σ aᵢbᵢ)² ≤ (Σ aᵢ²)(Σ bᵢ²)`,
经 Lagrange 恒等式 `ΣᵢΣⱼ (aᵢbⱼ − aⱼbᵢ)² = 2(Σa²)(Σb²) − 2(Σab)²` 证明. -/
theorem realCauchySchwarz {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑ i ∈ s, a i ^ 2) * (∑ i ∈ s, b i ^ 2) := by
  have hsq : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (a i * b j - a j * b i) ^ 2 := by
    refine Finset.sum_nonneg ?_
    intro i hi
    exact Finset.sum_nonneg (fun j hj => sq_nonneg _)
  have hsplit : (∑ i ∈ s, ∑ j ∈ s,
        (a i ^ 2 * b j ^ 2 + a j ^ 2 * b i ^ 2 - 2 * ((a i * b j) * (a j * b i)))) =
      (∑ i ∈ s, ∑ j ∈ s, a i ^ 2 * b j ^ 2) +
        (∑ i ∈ s, ∑ j ∈ s, a j ^ 2 * b i ^ 2) -
        (∑ i ∈ s, ∑ j ∈ s, 2 * ((a i * b j) * (a j * b i))) := by
    calc
      (∑ i ∈ s, ∑ j ∈ s,
          (a i ^ 2 * b j ^ 2 + a j ^ 2 * b i ^ 2 - 2 * ((a i * b j) * (a j * b i))))
          = ∑ i ∈ s, ((∑ j ∈ s, a i ^ 2 * b j ^ 2) +
                (∑ j ∈ s, a j ^ 2 * b i ^ 2) - (∑ j ∈ s, 2 * ((a i * b j) * (a j * b i)))) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ = (∑ i ∈ s, ∑ j ∈ s, a i ^ 2 * b j ^ 2) +
            (∑ i ∈ s, ∑ j ∈ s, a j ^ 2 * b i ^ 2) -
            (∑ i ∈ s, ∑ j ∈ s, 2 * ((a i * b j) * (a j * b i))) := by
            rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  have hidsum : (∑ i ∈ s, ∑ j ∈ s, (a i * b j - a j * b i) ^ 2) =
      2 * (∑ i ∈ s, a i ^ 2) * (∑ j ∈ s, b j ^ 2) - 2 * (∑ i ∈ s, a i * b i) ^ 2 := by
    calc
      (∑ i ∈ s, ∑ j ∈ s, (a i * b j - a j * b i) ^ 2)
          = ∑ i ∈ s, ∑ j ∈ s,
              (a i ^ 2 * b j ^ 2 + a j ^ 2 * b i ^ 2 - 2 * ((a i * b j) * (a j * b i))) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = (∑ i ∈ s, ∑ j ∈ s, a i ^ 2 * b j ^ 2) +
            (∑ i ∈ s, ∑ j ∈ s, a j ^ 2 * b i ^ 2) -
            (∑ i ∈ s, ∑ j ∈ s, 2 * ((a i * b j) * (a j * b i))) := by
            exact hsplit
      _ = (∑ i ∈ s, a i ^ 2) * (∑ j ∈ s, b j ^ 2) +
            (∑ i ∈ s, a i ^ 2) * (∑ j ∈ s, b j ^ 2) -
            2 * (∑ i ∈ s, a i * b i) * (∑ j ∈ s, a j * b j) := by
            have hT1 : (∑ i ∈ s, ∑ j ∈ s, a i ^ 2 * b j ^ 2) =
                (∑ i ∈ s, a i ^ 2) * (∑ j ∈ s, b j ^ 2) := by
              rw [← Finset.sum_mul_sum]
            have hT2 : (∑ i ∈ s, ∑ j ∈ s, a j ^ 2 * b i ^ 2) =
                (∑ i ∈ s, a i ^ 2) * (∑ j ∈ s, b j ^ 2) := by
              rw [Finset.sum_comm]
              rw [← Finset.sum_mul_sum]
            have hT3 : (∑ i ∈ s, ∑ j ∈ s, 2 * ((a i * b j) * (a j * b i))) =
                2 * (∑ i ∈ s, a i * b i) * (∑ j ∈ s, a j * b j) := by
              calc
                (∑ i ∈ s, ∑ j ∈ s, 2 * ((a i * b j) * (a j * b i)))
                    = ∑ i ∈ s, ∑ j ∈ s, (a i * b i) * (2 * (a j * b j)) := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      apply Finset.sum_congr rfl
                      intro j hj
                      ring
                _ = (∑ i ∈ s, a i * b i) * (∑ j ∈ s, 2 * (a j * b j)) := by
                      rw [← Finset.sum_mul_sum]
                _ = (∑ i ∈ s, a i * b i) * (2 * ∑ j ∈ s, a j * b j) := by
                      rw [← Finset.mul_sum]
                _ = 2 * (∑ i ∈ s, a i * b i) * (∑ j ∈ s, a j * b j) := by
                      ring
            rw [hT1, hT2, hT3]
      _ = 2 * (∑ i ∈ s, a i ^ 2) * (∑ j ∈ s, b j ^ 2) - 2 * (∑ i ∈ s, a i * b i) ^ 2 := by
            ring
  nlinarith

/-- **复数 Cauchy--Schwarz** (Finset):
`|Σᵢ xᵢ·conj(yᵢ)| ≤ √(Σ‖xᵢ‖²)·√(Σ‖yᵢ‖²)`, 经三角不等式与实数 C-S 证明. -/
theorem complexCauchySchwarz {ι : Type*} (s : Finset ι) (x y : ι → ℂ) :
    ‖∑ i ∈ s, x i * star (y i)‖ ≤
      Real.sqrt (∑ i ∈ s, ‖x i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2) := by
  have htri : ‖∑ i ∈ s, x i * star (y i)‖ ≤ ∑ i ∈ s, ‖x i * star (y i)‖ := by
    exact norm_sum_le s (fun i => x i * star (y i))
  have habs : (∑ i ∈ s, ‖x i * star (y i)‖) = ∑ i ∈ s, ‖x i‖ * ‖y i‖ := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [norm_mul, norm_star]
  have hA : 0 ≤ ∑ i ∈ s, ‖x i‖ ^ 2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hB : 0 ≤ ∑ i ∈ s, ‖y i‖ ^ 2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hcs : (∑ i ∈ s, ‖x i‖ * ‖y i‖) ^ 2 ≤
      (∑ i ∈ s, ‖x i‖ ^ 2) * (∑ i ∈ s, ‖y i‖ ^ 2) := by
    exact realCauchySchwarz s (fun i => ‖x i‖) (fun i => ‖y i‖)
  have hcs' : (∑ i ∈ s, ‖x i‖ * ‖y i‖) ≤
      Real.sqrt (∑ i ∈ s, ‖x i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2) := by
    have hsq : (∑ i ∈ s, ‖x i‖ * ‖y i‖) ^ 2 ≤
        (Real.sqrt (∑ i ∈ s, ‖x i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2)) ^ 2 := by
      nlinarith [hcs, Real.sq_sqrt hA, Real.sq_sqrt hB]
    have habs := (sq_le_sq).mp hsq
    have hc_nonneg : 0 ≤ ∑ i ∈ s, ‖x i‖ * ‖y i‖ :=
      Finset.sum_nonneg (fun i hi => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have hu_nonneg : 0 ≤ Real.sqrt (∑ i ∈ s, ‖x i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖y i‖ ^ 2) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rwa [abs_of_nonneg hc_nonneg, abs_of_nonneg hu_nonneg] at habs
  exact le_trans (le_trans htri (le_of_eq habs)) hcs'

/-- **大筛法对偶引理** (有限矩阵): 对任意 `A : ι → κ → ℂ` 与 `C ≥ 0`,
原形式 `Σᵢ |Σⱼ Aᵢⱼ aⱼ|² ≤ C·Σⱼ |aⱼ|² (∀a)` 与共轭转置对偶形式
`Σⱼ |Σᵢ conj(Aᵢⱼ) bᵢ|² ≤ C·Σᵢ |bᵢ|² (∀b)` 等价。

证明 (Montgomery 的经典论证): 设 `v = A*b` (`bStar`), 则
`‖A*b‖² = |⟨b, A A*b⟩| ≤ ‖A A*b‖·‖b‖ ≤ √C·‖A*b‖·‖b‖`, 由原形式
(作用于 `v`) 与复数 C-S 得到 `‖A*b‖ ≤ √C·‖b‖`; 反向由 `A** = A`
(`star (star A) = A`) 对称得到。 -/
theorem largeSieveDuality_primalToDual {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (A : ι → κ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hPrimal : ∀ a : κ → ℂ,
      ∑ i ∈ s, ‖∑ j ∈ t, A i j * a j‖ ^ 2 ≤ C * ∑ j ∈ t, ‖a j‖ ^ 2) :
    ∀ b : ι → ℂ,
      ∑ j ∈ t, ‖∑ i ∈ s, star (A i j) * b i‖ ^ 2 ≤ C * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  intro b
  let bStar : κ → ℂ := fun j => ∑ i ∈ s, star (A i j) * b i
  let AAb : ι → ℂ := fun i => ∑ j ∈ t, A i j * bStar j
  have hsquare : (∑ j ∈ t, ‖bStar j‖ ^ 2) =
      ‖∑ i ∈ s, b i * star (AAb i)‖ := by
    have hnonneg : 0 ≤ (∑ j ∈ t, ‖bStar j‖ ^ 2 : ℝ) :=
      Finset.sum_nonneg (fun j hj => sq_nonneg _)
    symm
    calc
      ‖∑ i ∈ s, b i * star (AAb i)‖
          = ‖∑ i ∈ s, ∑ j ∈ t, b i * star (A i j) * star (bStar j)‖ := by
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            calc
              b i * star (∑ j ∈ t, A i j * bStar j)
                  = b i * (∑ j ∈ t, star (A i j) * star (bStar j)) := by
                    congr 1
                    exact (map_sum (starRingEnd ℂ) (fun j => A i j * bStar j) t).trans
                      (Finset.sum_congr rfl (fun j hj =>
                        map_mul (starRingEnd ℂ) (A i j) (bStar j)))
              _ = ∑ j ∈ t, b i * (star (A i j) * star (bStar j)) := by
                    rw [Finset.mul_sum]
              _ = ∑ j ∈ t, b i * star (A i j) * star (bStar j) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    rw [← mul_assoc]
      _ = ‖∑ j ∈ t, ∑ i ∈ s, b i * star (A i j) * star (bStar j)‖ := by
            congr 1
            rw [Finset.sum_comm]
      _ = ‖∑ j ∈ t, (∑ i ∈ s, b i * star (A i j)) * star (bStar j)‖ := by
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            rw [← Finset.sum_mul]
      _ = ‖∑ j ∈ t, (∑ i ∈ s, star (A i j) * b i) * star (bStar j)‖ := by
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            simp [mul_comm]
      _ = ‖∑ j ∈ t, bStar j * star (bStar j)‖ := rfl
      _ = ‖((∑ j ∈ t, ‖bStar j‖ ^ 2 : ℝ) : ℂ)‖ := by
            congr 1
            rw [Complex.ofReal_sum]
            apply Finset.sum_congr rfl
            intro j hj
            exact (Complex.mul_conj (bStar j)).trans (by rw [Complex.normSq_eq_norm_sq])
      _ = ∑ j ∈ t, ‖bStar j‖ ^ 2 := by
            rw [Complex.norm_real, Real.norm_of_nonneg hnonneg]
  have hcs : ‖∑ i ∈ s, b i * star (AAb i)‖ ≤
      Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖AAb i‖ ^ 2) := by
    exact complexCauchySchwarz s b AAb
  have hnorm : (∑ i ∈ s, ‖AAb i‖ ^ 2) ≤ C * ∑ j ∈ t, ‖bStar j‖ ^ 2 := by
    simpa [AAb] using hPrimal bStar
  have hchain : (∑ j ∈ t, ‖bStar j‖ ^ 2) ≤
      Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2) * Real.sqrt (C * ∑ j ∈ t, ‖bStar j‖ ^ 2) := by
    calc
      (∑ j ∈ t, ‖bStar j‖ ^ 2) = ‖∑ i ∈ s, b i * star (AAb i)‖ := hsquare
      _ ≤
          Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖AAb i‖ ^ 2) := hcs
      _ ≤ Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2) * Real.sqrt (C * ∑ j ∈ t, ‖bStar j‖ ^ 2) := by
            apply mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
            have hCD : 0 ≤ C * ∑ j ∈ t, ‖bStar j‖ ^ 2 :=
              mul_nonneg hC (Finset.sum_nonneg (fun j hj => sq_nonneg _))
            exact (Real.sqrt_le_sqrt_iff hCD).2 hnorm
  by_cases hD0 : (∑ j ∈ t, ‖bStar j‖ ^ 2) = 0
  · rw [hD0]
    exact mul_nonneg hC (Finset.sum_nonneg (fun i hi => sq_nonneg _))
  · have hDpos : 0 < (∑ j ∈ t, ‖bStar j‖ ^ 2) :=
      lt_of_le_of_ne (Finset.sum_nonneg (fun j hj => sq_nonneg _)) (Ne.symm hD0)
    have hS : 0 ≤ ∑ i ∈ s, ‖b i‖ ^ 2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
    have hCD : 0 ≤ C * ∑ j ∈ t, ‖bStar j‖ ^ 2 :=
      mul_nonneg hC (Finset.sum_nonneg (fun j hj => sq_nonneg _))
    have hsq2 : (∑ j ∈ t, ‖bStar j‖ ^ 2) ^ 2 ≤
        C * (∑ i ∈ s, ‖b i‖ ^ 2) * (∑ j ∈ t, ‖bStar j‖ ^ 2) := by
      have hsq2' : (∑ j ∈ t, ‖bStar j‖ ^ 2) ^ 2 ≤
          (Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2) * Real.sqrt (C * ∑ j ∈ t, ‖bStar j‖ ^ 2)) ^ 2 := by
        have hD_nonneg : 0 ≤ ∑ j ∈ t, ‖bStar j‖ ^ 2 :=
          Finset.sum_nonneg (fun j hj => sq_nonneg _)
        have hu_nonneg : 0 ≤ Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2) *
            Real.sqrt (C * ∑ j ∈ t, ‖bStar j‖ ^ 2) :=
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        have habs : |∑ j ∈ t, ‖bStar j‖ ^ 2| ≤
            |Real.sqrt (∑ i ∈ s, ‖b i‖ ^ 2) * Real.sqrt (C * ∑ j ∈ t, ‖bStar j‖ ^ 2)| := by
          rwa [abs_of_nonneg hD_nonneg, abs_of_nonneg hu_nonneg]
        exact (sq_le_sq).mpr habs
      nlinarith [hsq2', Real.sq_sqrt hS, Real.sq_sqrt hCD]
    nlinarith

/-- **大筛法对偶引理**: 原形式与对偶形式的等价性.
(反向方向把 `A` 换成其共轭转置, 由 `star (star x) = x` 回到原形式.) -/
theorem largeSieveDuality {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (A : ι → κ → ℂ) {C : ℝ} (hC : 0 ≤ C) :
    (∀ a : κ → ℂ, ∑ i ∈ s, ‖∑ j ∈ t, A i j * a j‖ ^ 2 ≤ C * ∑ j ∈ t, ‖a j‖ ^ 2) ↔
      (∀ b : ι → ℂ, ∑ j ∈ t, ‖∑ i ∈ s, star (A i j) * b i‖ ^ 2 ≤ C * ∑ i ∈ s, ‖b i‖ ^ 2) := by
  constructor
  · exact largeSieveDuality_primalToDual s t A hC
  · intro hDual a
    have hPrim := largeSieveDuality_primalToDual (s := t) (t := s)
      (A := fun j i => star (A i j)) hC hDual
    simpa [star_star] using hPrim a

/-- **加法大筛: 原形式 ⟺ 对偶形式**. 本推论把通用对偶引理应用到
特征矩阵 `A x n = e(nx)` 上 (`C = N + 1/δ`), 因此两个目标陈述在研究层面
是等价的: 证明任一形式即得另一形式. -/
theorem montgomeryDuality (M : ℤ) (N : ℕ) :
    MontgomeryLargeSievePrimal M N ↔ MontgomeryLargeSieveDual M N := by
  have hC : ∀ δ : ℝ, 0 < δ → 0 ≤ (N : ℝ) + 1 / δ := by
    intro δ hδ
    positivity
  constructor
  · intro hprimal δ hδ X hws b
    have hpr : ∀ a : ℤ → ℂ, ∑ x ∈ X,
        ‖∑ n ∈ Finset.Icc (M + 1) (M + N), (charPow n x : ℂ) * a n‖ ^ 2 ≤
          ((N : ℝ) + 1 / δ) * ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖a n‖ ^ 2 := by
      simpa [circleCharSum, mul_comm] using hprimal δ hδ X hws
    have hdual := (largeSieveDuality (s := X) (t := Finset.Icc (M + 1) (M + N))
      (A := fun x n => (charPow n x : ℂ)) (hC δ hδ)).1 hpr
    exact hdual b
  · intro hdual δ hδ X hws a
    have hpr := (largeSieveDuality (s := X) (t := Finset.Icc (M + 1) (M + N))
      (A := fun x n => (charPow n x : ℂ)) (hC δ hδ)).2 (hdual δ hδ X hws)
    simpa [circleCharSum, mul_comm] using hpr a

end

end AnalyticNumberTheory.LargeSieve
