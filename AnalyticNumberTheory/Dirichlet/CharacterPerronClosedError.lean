import AnalyticNumberTheory.Dirichlet.CharacterPerron
import LiuWang.Proof.ExplicitPerron.NearSum

/-!
# Closed half-integer character Perron error

This module extracts the dependency-small half-integer central-sum estimate from
exact-same-pin Liu--Wang and composes it with ANT's existing sharp character
Perron wrapper.  It keeps the direct finite twisted-von-Mangoldt endpoint and
eliminates the remaining finite `centralCost` from the displayed error.

The generic half-integer geometry remains in the original Liu--Wang namespace;
the actual-character theorem below is a thin ANT adapter.  No contour theorem,
zero count, GRH premise, or application-specific parameter is introduced.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace AnalyticNumberTheory.Dirichlet

private theorem halfHarmonic_le_log_of_pos {m : ℕ} (hm : 1 ≤ m) :
    LiuWang.Proof.ExplicitPerron.halfHarmonic m ≤ 3 + Real.log (m : ℝ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hm)
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
    LiuWang.Proof.ExplicitPerron.halfHarmonic_le_log k

/-- A closed scalar majorant for the sharp character-Perron error at a
half-integer endpoint. -/
def characterPerronClosedHalfError (x b T : ℝ) : ℝ :=
  (x ^ b / Real.log 2 * ((Real.log 4 + 4) * b / (b - 1)) +
    x * (2 ^ b * Real.log x * (Real.log x + 3) +
      Real.log (2 * x) * (Real.log (2 * x) + 3))) / (Real.pi * T)

/-- The twisted-von-Mangoldt central cost at a positive half-integer is bounded
by the same closed logarithmic expression as the untwisted Liu--Wang source.
The character twist is absorbed by `‖χ(n)‖ ≤ 1` and `Λ(n) ≤ log n`. -/
theorem centralCost_twisted_halfInteger_le_closed
    {q : ℕ} (χ : DirichletCharacter ℂ q) {m : ℕ} (hm : 1 ≤ m)
    {b : ℝ} (hb : 1 ≤ b) :
    LiuWang.Proof.ExplicitPerron.centralCost
        (twistedMangoldtSequence χ) ((m : ℝ) + 1 / 2) b ≤
      ((m : ℝ) + 1 / 2) *
        (2 ^ b * Real.log ((m : ℝ) + 1 / 2) *
            (Real.log ((m : ℝ) + 1 / 2) + 3) +
          Real.log (2 * ((m : ℝ) + 1 / 2)) *
            (Real.log (2 * ((m : ℝ) + 1 / 2)) + 3)) := by
  let x : ℝ := (m : ℝ) + 1 / 2
  let A : ℝ → ℝ := fun u => Real.log (max 1 u)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx1 : 1 ≤ x := by dsimp [x]; linarith
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hA : Monotone A := by
    intro u v huv
    exact Real.log_le_log (zero_lt_one.trans_le (le_max_left _ _))
      (max_le_max_left 1 huv)
  have ha : ∀ n : ℕ, 1 ≤ n → ‖twistedMangoldtSequence χ n‖ ≤ A n := by
    intro n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp [A]
    rw [max_eq_right hnR]
    exact (norm_twistedMangoldtSequence_le_vonMangoldt χ n).trans
      ArithmeticFunction.vonMangoldt_le_log
  have h := LiuWang.Proof.ExplicitPerron.centralCost_halfInteger_le
    (twistedMangoldtSequence χ) A hA ha hm hb
  change LiuWang.Proof.ExplicitPerron.centralCost
      (twistedMangoldtSequence χ) x b ≤
    2 ^ b * A x * x * LiuWang.Proof.ExplicitPerron.halfHarmonic m +
      A (2 * x) * x * LiuWang.Proof.ExplicitPerron.halfHarmonic (m + 1) at h
  simp only [A, max_eq_right hx1,
    max_eq_right (show 1 ≤ 2 * x by linarith)] at h
  have hlo : LiuWang.Proof.ExplicitPerron.halfHarmonic m ≤ Real.log x + 3 := by
    have hlog := Real.log_le_log (by linarith : (0 : ℝ) < m)
      (show (m : ℝ) ≤ x by dsimp [x]; linarith)
    linarith [halfHarmonic_le_log_of_pos hm]
  have hhi : LiuWang.Proof.ExplicitPerron.halfHarmonic (m + 1) ≤
      Real.log (2 * x) + 3 := by
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < m + 1)
      (show (m : ℝ) + 1 ≤ 2 * x by dsimp [x]; linarith)
    linarith [LiuWang.Proof.ExplicitPerron.halfHarmonic_le_log m]
  change LiuWang.Proof.ExplicitPerron.centralCost
      (twistedMangoldtSequence χ) x b ≤
    x * (2 ^ b * Real.log x * (Real.log x + 3) +
      Real.log (2 * x) * (Real.log (2 * x) + 3))
  apply h.trans
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hl := mul_le_mul_of_nonneg_left hlo
    (show 0 ≤ 2 ^ b * Real.log x * x by positivity)
  have hu := mul_le_mul_of_nonneg_left hhi
    (show 0 ≤ Real.log (2 * x) * x by
      exact mul_nonneg (Real.log_nonneg (by linarith)) hx0.le)
  nlinarith

/-- Closed sharp-Perron error for an actual Dirichlet character at the canonical
half-integer endpoint.  The finite central sum is eliminated. -/
theorem norm_characterPerron_sub_partialSum_le_closed_halfInteger
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {m : ℕ} (hm : 1 ≤ m)
    {b T : ℝ} (hb : 1 < b) (hT : 0 < T) :
    ‖LiuWang.Proof.ExplicitPerron.vertical
        (characterPerronIntegrand χ ((m : ℝ) + 1 / 2)) b (-T) T -
      twistedMangoldtPartialSum χ ((m : ℝ) + 1 / 2)‖ ≤
      characterPerronClosedHalfError ((m : ℝ) + 1 / 2) b T := by
  have hx : 0 < (m : ℝ) + 1 / 2 := by positivity
  have hbase := norm_characterPerron_sub_partialSum_le χ hx
    (fun n => LiuWang.Proof.ExplicitPerron.halfInteger_ne_nat m n) hb hT
  apply hbase.trans
  unfold characterPerronClosedHalfError
  gcongr
  exact centralCost_twisted_halfInteger_le_closed χ hm hb.le

end AnalyticNumberTheory.Dirichlet
