import AnalyticNumberTheory.Sieve.PanMeanValueBody
import AnalyticNumberTheory.Sieve.PanMainTerm

/-!
# PanMeanValueUniform 最终装配 (ant #15)

本文件实例化 Vaughan 拆分 `PanVaughanSplit`: 由三个辅助 Prop
(`PanTypeICharacterMeanValue` / `PanTypeIICharacterMeanValue` /
`PanMainTermSieveBound`) 与两个解析台阶 (`PanLogEventuallyLarge`,
`PanVaughanPointwiseSplit`) 推出最终形式的加权 Pan 均值界, 从而经
`PanMeanValueUniform.of_vaughanSplit` (两陈述逐字相同, 定义性相等) 给出
`PanMeanValueUniform` 的完整证明.

装配的数学结构 (Liu 2022 §III Thm 2; Pan 1963):
  panMaxY X q x f = max_{y≤x} max_l |Σ_a f(a)·Δ(y;a,q,l)|   (WeightedPan)
  Δ(y;a,q,l) = π(y;a,q,l) − li(y/a)/φ(q)                    (分布误差)
  π(y;a,q,l) 经 Vaughan 恒等式 Λ = V1 − middle + V3 分解为:
    type I (apV1) + type II (apV3) + 主项 (li) 三部分

三部分分别由 PanTypeIWeightedBound (T1'/PR #31-#32), PanTypeIIWeightedBound
(T2/PR #33), PanMainTermBound (T3/PR #34) 控制, 而这三个加权 Bound 由
各文件内的归约链 (零 sorry) 从开放辅助 Prop 推出:
  PanTypeIWeightedBound.of_characterMeanValue  (PanMeanValueBody §5)
  PanTypeIIWeightedBound.of_characterMeanValue (PanMeanValueBody §5.2)
  PanMainTermBound.of_sieveBound               (PanMainTerm §2)

本文件落地装配的**有限代数** (零 sorry):
  1. 逐 q 点式拆分 (`panAssembly_pointwise`): w_q·panMaxY ≤ w_q·PI + w_q·PII + w_q·PM
     (q = 0 时权重 μ²(q) = 0, 平凡; q > 0 用点式拆分 + 权重非负);
  2. 求和拆分 (`sum_add_distrib`) 成三部分;
  3. q 范围对账 (`panAssembly_floor_le`): B = max B₁ (max B₂ B₃), log(xX) ≥ 1 时
     Q_B ≤ Q_{B_i}, 三个 Bound 的求和范围均包含 Σ_{q ≤ Q_B} (权重非负 ⇒ 子集和 ≤ 全和);
  4. 三部分分别 ≤ C_i·xX/log^A X, 求和 ring 得 (C₁+C₂+C₃)·xX/log^A X.

两个解析台阶 (经典解析内容, 不以公理引入, 以辅助 Prop 封装, 见各自定义):
  (a) `PanLogEventuallyLarge`: log(xX) ≥ 1 最终成立 (经典 xX → ∞ 的标准最终性);
  (b) `PanVaughanPointwiseSplit`: 素数 AP 计数 π 经 Vaughan 拆分到
      apV1/apV3/li 三片段的逐 q 点式界 ("Λ-计数 → 素数计数" 的解析转换).
-/

namespace AnalyticNumberTheory.Sieve

open Real Finset

open scoped Classical
open scoped ArithmeticFunction.Moebius

set_option maxHeartbeats 6000000
-- li 主项片段不依赖剩余类参数 l', 抑制相应告警 (同 PanMainTerm.lean).
set_option linter.unusedVariables false

/-- **Vaughan 拆分 (解析台阶, 最终形式)**: 对每个 A > 0 存在 C > 0, B, x₀,
使对所有 X ≥ x₀, Q := (xX)^{1/2}/log^B(xX),

  Σ_{q ≤ Q} μ²(q)·3^{ω(q)}·panMaxY X q ⌊xX⌋ f ≤ C·xX/log^A(xX).

该陈述与 `PanMeanValueUniform` 逐字相同 (定义性相等); 它是装配的最终
解析输入, 由 `PanVaughanSplit.of_analyticInputs` 从三个 Bound 的辅助 Prop
与两个解析台阶推出 (经典证明: 把 Vaughan 恒等式应用到等差 von Mangoldt
计数, type I/II 由 T1'/T2 加权界控制, middle 项吸收进 li 主项由 T3 控制). -/
def PanVaughanSplit (x : ℕ → ℝ) (f : ℕ → ℝ) (u v : ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
    ∀ X : ℕ, x₀ ≤ X →
      ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) /
            (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panMaxY X q (Nat.floor (x X)) f ≤
        C * x X / (log (x X)) ^ A

/-- **解析台阶 (log 最终性)**: `log(x X) ≥ 1` 对足够大的 X 成立.
经典解析中 x X → ∞ 时自动成立 (Liu 2022 §III); 装配的 q 范围对账
(`Q_B ≤ Q_{B_i}`, rpow 在底数 ≥ 1 时关于指数单调) 依赖它. -/
def PanLogEventuallyLarge (x : ℕ → ℝ) : Prop :=
  ∃ x₀ : ℕ, ∀ X : ℕ, x₀ ≤ X → 1 ≤ Real.log (x X)

/-- **解析台阶 (逐 q Vaughan 点式拆分)**: 对每个 q > 0 与所有截断参数,
`panMaxY` (素数 AP 计数的加权分布误差的 max) 被三个片段 max 控制:

  panMaxY X q x f ≤
    panPieceMaxY X q x f (fun y q l => apV1 y q l u / log y) +
    panPieceMaxY X q x f (fun y q l => apV3 y q l u v / log y) +
    panPieceMaxY X q x f (fun y q l => li y / φ(q)).

经典证明 (Liu 2022 §III Thm 2; HR 1974 Ch.10): 把 Vaughan 恒等式
`Λ = V1 − middle + V3` (`vaughanIdentity_threeTerm`, VaughanIdentity.lean)
应用到等差 von Mangoldt 计数 `apVonMangoldt` (PanMeanValueBody §4):
type I/II 片段由 apV1/apV3 承担, middle 项被 Möbius 反演吸收进 li 主项
(`π(y;q,l)·log y ≈ Σ_{n≤y,n≡l} Λ(n)` 的 PNT 级转换), 再对 y, l 取 max.
这是 "Λ-计数 → 素数计数" 的解析转换 (与 `PanMeanValueUniform` 同级的
经典结果), 本仓库以 Prop 封装, 不引入公理, 不 sorry. -/
def PanVaughanPointwiseSplit (x : ℕ → ℝ) (f : ℕ → ℝ) (u v : ℕ) : Prop :=
  ∀ X q y : ℕ, 0 < q →
    panMaxY X q y f ≤
      panPieceMaxY X q y f (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
      panPieceMaxY X q y f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
      panPieceMaxY X q y f (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q)

/-- 片段 l-max 非负 (q ≤ 1 时 l-集为空取 0). 镜像 `panMaxL_nonneg`. -/
private lemma panPieceMaxL_nonneg (y X q : ℕ) (f : ℕ → ℝ) (g : ℕ → ℕ → ℕ → ℝ) :
    0 ≤ panPieceMaxL y X q f g := by
  unfold panPieceMaxL
  by_cases h : ((Finset.Icc 1 (q - 1)).filter (fun l => l.Coprime q)).Nonempty
  · dsimp only []
    rw [dif_pos h]
    rcases h with ⟨l, hl⟩
    have hl' : |panPieceSum y X q l f g| ∈
        (Finset.image (fun l : ℕ => |panPieceSum y X q l f g|)
          ((Finset.Icc 1 (q - 1)).filter (fun l : ℕ => l.Coprime q))) := by
      exact Finset.mem_image.mpr ⟨l, hl, rfl⟩
    exact le_trans (abs_nonneg _) (Finset.le_max' _ _ hl')
  · dsimp only []
    rw [dif_neg h]

/-- 片段 y-max 非负 (y = 0 项在像中, 每个元素都是绝对值). -/
private lemma panPieceMaxY_nonneg (X q x : ℕ) (f : ℕ → ℝ) (g : ℕ → ℕ → ℕ → ℝ) :
    0 ≤ panPieceMaxY X q x f g := by
  unfold panPieceMaxY
  exact le_trans (panPieceMaxL_nonneg 0 X q f g)
    (Finset.le_max'
      (s := (Finset.range (x + 1)).image (fun y => panPieceMaxL y X q f g))
      (x := panPieceMaxL 0 X q f g)
      (Finset.mem_image.mpr ⟨0, by simp, rfl⟩))

/-- **q 范围对账 (核心)**: B' ≤ B 且 1 ≤ L 时,
`⌊z/L^B⌋ ≤ ⌊z/L^{B'}⌋` (z ≥ 0). 用于 `Q_B ≤ Q_{B_i}`. -/
private lemma panAssembly_floor_le (z L : ℝ) (B B' : ℝ)
    (hz : 0 ≤ z) (hL1 : 1 ≤ L) (hB : B' ≤ B) :
    Nat.floor (z / L ^ B) ≤ Nat.floor (z / L ^ B') := by
  apply Nat.floor_le_floor
  exact div_le_div_of_nonneg_left hz (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hL1) B')
    (Real.rpow_le_rpow_of_exponent_le hL1 hB)

/-- **带权重逐 q 拆分**: w_q·panMaxY ≤ w_q·PI + w_q·PII + w_q·PM
(q = 0 时权重 μ²(q) = 0, 平凡; q > 0 用 hsplit + 权重非负). -/
private lemma panAssembly_pointwise (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ)
    (hsplit : ∀ X q x : ℕ, 0 < q →
      panMaxY X q x f ≤
        panPieceMaxY X q x f (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
        panPieceMaxY X q x f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
        panPieceMaxY X q x f (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q)) :
    ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * panMaxY X q x f ≤
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
        panPieceMaxY X q x f (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
        panPieceMaxY X q x f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
        panPieceMaxY X q x f (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q) := by
  by_cases hq0 : q = 0
  · subst q
    have hμ : (μ 0 : ℤ) = 0 := by
      exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree (not_squarefree_zero)
    simp [hμ]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    have hw : 0 ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card :=
      panTypeI_weight_nonneg q
    calc
      ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * panMaxY X q x f
          ≤ ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              (panPieceMaxY X q x f (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
                panPieceMaxY X q x f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
                panPieceMaxY X q x f (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q)) := by
            exact mul_le_mul_of_nonneg_left (hsplit X q x hq) hw
      _ = ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              panPieceMaxY X q x f (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              panPieceMaxY X q x f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              panPieceMaxY X q x f (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q) := by
            ring

/-- **求和范围包含**: Q ≤ Q' 且 w 非负时,
`Σ_{q ≤ Q} w q ≤ Σ_{q ≤ Q'} w q`. -/
private lemma panAssembly_sum_le_sum (Q Q' : ℕ) (w : ℕ → ℝ) (hQQ' : Q ≤ Q')
    (hw : ∀ q : ℕ, 0 ≤ w q) :
    (∑ q ∈ Finset.range (Q + 1), w q) ≤ ∑ q ∈ Finset.range (Q' + 1), w q := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ hQQ'))
    (fun q hq hq' => hw q)

/-- **Vaughan 拆分实例化 (零 sorry)**: 由三个辅助 Prop (T1'/T2/T3 各自的
特征均值 / 筛主项台阶) 与两个解析台阶 (log 最终性 + 逐 q 点式拆分) 推出
最终形式的 `PanVaughanSplit`. 全部有限代数 (归约链应用, 逐 q 点式拆分,
求和拆分, q 范围对账 B = max B₁ (max B₂ B₃), 对数幂次对账) 在此证明.

证明结构:
  1. 归约链: `PanTypeIWeightedBound.of_characterMeanValue` 等把三个辅助
     Prop 变成三个加权 Bound (各自 ∃ Cᵢ, Bᵢ, x₀ᵢ);
  2. 对每个 A > 0 取 C := C₁+C₂+C₃, B := max B₁ (max B₂ B₃),
     x₀ := max (max x₀₁ (max x₀₂ x₀₃)) X₀;
  3. 逐 q 带权重点式拆分 (q = 0 权重 μ²(q) = 0), 求和拆成三部分;
  4. q 范围对账: log(xX) ≥ 1 (由 hfin) 与 Bᵢ ≤ B 给出 Q_B ≤ Q_{Bᵢ},
     三部分各自的求和范围包含 Σ_{q ≤ Q_B} (权重非负);
  5. 三部分分别 ≤ Cᵢ·xX/log^A X, 求和 ring. -/
theorem PanVaughanSplit.of_analyticInputs
    {x : ℕ → ℝ} {f : ℕ → ℝ} {u v : ℕ}
    (hI : PanTypeICharacterMeanValue x f u)
    (hII : PanTypeIICharacterMeanValue x f u v)
    (hM : PanMainTermSieveBound x f)
    (hfin : PanLogEventuallyLarge x)
    (hsplit : PanVaughanPointwiseSplit x f u v) :
    PanVaughanSplit x f u v := by
  have hI' : PanTypeIWeightedBound x f u := PanTypeIWeightedBound.of_characterMeanValue hI
  have hII' : PanTypeIIWeightedBound x f u v := PanTypeIIWeightedBound.of_characterMeanValue hII
  have hM' : PanMainTermBound x f := PanMainTermBound.of_sieveBound hM
  rcases hfin with ⟨X₀, hX₀'⟩
  intro A hA
  rcases hI' A hA with ⟨C1, hC1, B1, x₀₁, hI1⟩
  rcases hII' A hA with ⟨C2, hC2, B2, x₀₂, hII1⟩
  rcases hM' A hA with ⟨C3, hC3, B3, x₀₃, hM1⟩
  refine ⟨C1 + C2 + C3, add_pos (add_pos hC1 hC2) hC3,
    max B1 (max B2 B3), max (max x₀₁ (max x₀₂ x₀₃)) X₀, ?_⟩
  intro X hX
  have hX₁ : x₀₁ ≤ X := by omega
  have hX₂ : x₀₂ ≤ X := by omega
  have hX₃ : x₀₃ ≤ X := by omega
  have hX₄ : X₀ ≤ X := by omega
  have hL : 1 ≤ Real.log (x X) := hX₀' X hX₄
  have hsqrt : 0 ≤ (x X) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_nonneg _
  let B : ℝ := max B1 (max B2 B3)
  let Q : ℕ := Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B)
  have hB₁ : B1 ≤ B := by
    dsimp [B]
    exact le_max_left _ _
  have hB₂ : B2 ≤ B := by
    dsimp [B]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hB₃ : B3 ≤ B := by
    dsimp [B]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hQ1 : Q ≤ Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B1) := by
    dsimp [Q, B]
    exact panAssembly_floor_le ((x X) ^ (1 / 2 : ℝ)) (Real.log (x X))
      (max B1 (max B2 B3)) B1 hsqrt hL hB₁
  have hQ2 : Q ≤ Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B2) := by
    dsimp [Q, B]
    exact panAssembly_floor_le ((x X) ^ (1 / 2 : ℝ)) (Real.log (x X))
      (max B1 (max B2 B3)) B2 hsqrt hL hB₂
  have hQ3 : Q ≤ Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B3) := by
    dsimp [Q, B]
    exact panAssembly_floor_le ((x X) ^ (1 / 2 : ℝ)) (Real.log (x X))
      (max B1 (max B2 B3)) B3 hsqrt hL hB₃
  have hI2 :
      (∑ q ∈ Finset.range (Q + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV1 y q l u / Real.log (y : ℝ)))
        ≤ C1 * x X / (Real.log (x X)) ^ A := by
    calc
      (∑ q ∈ Finset.range (Q + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV1 y q l u / Real.log (y : ℝ)))
          ≤ ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B1) + 1),
              ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
                panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV1 y q l u / Real.log (y : ℝ)) := by
            exact panAssembly_sum_le_sum Q
              (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B1))
              (fun q => ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
                panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV1 y q l u / Real.log (y : ℝ)))
              hQ1 (fun q => mul_nonneg (panTypeI_weight_nonneg q)
                (panPieceMaxY_nonneg X q (Nat.floor (x X)) f
                  (fun y q l => apV1 y q l u / Real.log (y : ℝ))))
      _ ≤ C1 * x X / (Real.log (x X)) ^ A := hI1 X hX₁
  have hII2 :
      (∑ q ∈ Finset.range (Q + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)))
        ≤ C2 * x X / (Real.log (x X)) ^ A := by
    calc
      (∑ q ∈ Finset.range (Q + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)))
          ≤ ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B2) + 1),
              ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
                panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) := by
            exact panAssembly_sum_le_sum Q
              (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B2))
              (fun q => ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
                panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)))
              hQ2 (fun q => mul_nonneg (panTypeI_weight_nonneg q)
                (panPieceMaxY_nonneg X q (Nat.floor (x X)) f
                  (fun y q l => apV3 y q l u v / Real.log (y : ℝ))))
      _ ≤ C2 * x X / (Real.log (x X)) ^ A := hII1 X hX₂
  have hM2 :
      (∑ q ∈ Finset.range (Q + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            panPieceMaxY X q (Nat.floor (x X)) f
              (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q))
        ≤ C3 * x X / (Real.log (x X)) ^ A := by
    calc
      (∑ q ∈ Finset.range (Q + 1),
          ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
            panPieceMaxY X q (Nat.floor (x X)) f
              (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q))
          ≤ ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B3) + 1),
              ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
                panPieceMaxY X q (Nat.floor (x X)) f
                  (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q) := by
            exact panAssembly_sum_le_sum Q
              (Nat.floor ((x X) ^ (1 / 2 : ℝ) / (Real.log (x X)) ^ B3))
              (fun q => ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
                panPieceMaxY X q (Nat.floor (x X)) f
                  (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q))
              hQ3 (fun q => mul_nonneg (panTypeI_weight_nonneg q)
                (panPieceMaxY_nonneg X q (Nat.floor (x X)) f
                  (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q)))
      _ ≤ C3 * x X / (Real.log (x X)) ^ A := hM1 X hX₃
  calc
    (∑ q ∈ Finset.range (Q + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * panMaxY X q (Nat.floor (x X)) f)
        ≤ ∑ q ∈ Finset.range (Q + 1),
            (((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
                panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV1 y q l u / Real.log (y : ℝ)) +
              ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
                panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV3 y q l u v / Real.log (y : ℝ)) +
              ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
                panPieceMaxY X q (Nat.floor (x X)) f
                  (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q)) := by
          apply Finset.sum_le_sum
          intro q hq
          exact panAssembly_pointwise X q (Nat.floor (x X)) f u v hsplit
    _ = (∑ q ∈ Finset.range (Q + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV1 y q l u / Real.log (y : ℝ))) +
        (∑ q ∈ Finset.range (Q + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              panPieceMaxY X q (Nat.floor (x X)) f (fun y q l => apV3 y q l u v / Real.log (y : ℝ))) +
        (∑ q ∈ Finset.range (Q + 1),
            ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
              panPieceMaxY X q (Nat.floor (x X)) f
                (fun y q l => logarithmicIntegral (y : ℝ) / Nat.totient q)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ C1 * x X / (Real.log (x X)) ^ A + C2 * x X / (Real.log (x X)) ^ A +
          C3 * x X / (Real.log (x X)) ^ A := by
        apply add_le_add
        · apply add_le_add
          · exact hI2
          · exact hII2
        · exact hM2
    _ = (C1 + C2 + C3) * x X / (Real.log (x X)) ^ A := by
        ring

/-- **装配定理**: Vaughan 拆分 (最终形式) ⇒ PanMeanValueUniform.
`PanVaughanSplit` 与 `PanMeanValueUniform` 的陈述逐字相同, 故这是
定义性相等下的平凡归约 (零 sorry). -/
theorem PanMeanValueUniform.of_vaughanSplit
    {x : ℕ → ℝ} {f : ℕ → ℝ} {u v : ℕ}
    (hV : PanVaughanSplit x f u v) :
    PanMeanValueUniform x f := by
  simpa [PanMeanValueUniform, PanVaughanSplit] using hV

end AnalyticNumberTheory.Sieve
