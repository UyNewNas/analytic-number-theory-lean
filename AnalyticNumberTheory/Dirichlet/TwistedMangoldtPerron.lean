import LiuWang.Proof.ExplicitPerron.Mangoldt
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Twisted von Mangoldt Perron core

Minimal project-neutral character layer needed before the sharp character-Perron
wrapper.  It deliberately avoids the larger zero-free/Vaughan endpoint hierarchy.

The definitions and proofs are provenance-preserving adaptations of the exact-same-pin
Liu--Wang explicit-Perron sources.  The logarithmic-derivative identity is only a
thin adapter over Mathlib's `DirichletCharacter.LSeries_twist_vonMangoldt_eq`.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace AnalyticNumberTheory.Dirichlet

/-- Dirichlet-character twist of the von Mangoldt coefficients. -/
def twistedMangoldtSequence {q : ℕ}
    (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ n * (ArithmeticFunction.vonMangoldt n : ℂ)

/-- Twisting by a Dirichlet character cannot increase a von Mangoldt coefficient. -/
theorem norm_twistedMangoldtSequence_le_vonMangoldt
    {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖twistedMangoldtSequence χ n‖ ≤ ArithmeticFunction.vonMangoldt n := by
  unfold twistedMangoldtSequence
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
    (χ.norm_le_one n)

/-- Absolute convergence of the twisted von Mangoldt series on `Re(s) > 1`. -/
theorem twistedMangoldt_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (twistedMangoldtSequence χ) s := by
  exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs

/-- On the half-plane of absolute convergence, `-L'/L` is the twisted
von Mangoldt L-series. -/
theorem neg_logDeriv_LFunction_eq_twistedMangoldtLSeries
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    -logDeriv χ.LFunction s = LSeries (twistedMangoldtSequence χ) s := by
  have hSeries := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  rw [logDeriv_apply,
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hSequence : twistedMangoldtSequence χ =
      (fun n : ℕ => χ n) *
        (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) := by
    funext n
    rfl
  rw [hSequence, ← neg_div]
  exact hSeries.symm

/-- Explicit character-uniform norm-series bound inherited from the untwisted
von Mangoldt series. -/
theorem twistedMangoldt_normSum_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    {b : ℝ} (hb : 1 < b) :
    (∑' n, ‖LSeries.term (twistedMangoldtSequence χ) (b : ℂ) n‖) ≤
      (Real.log 4 + 4) * b / (b - 1) := by
  apply le_trans _ (LiuWang.Proof.ExplicitPerron.mangoldt_normSum_le hb)
  apply (twistedMangoldt_summable χ (by simpa using hb)).norm.tsum_le_tsum
  · intro n
    apply LSeries.norm_term_le
    simpa only [Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] using
      norm_twistedMangoldtSequence_le_vonMangoldt χ n
  · exact (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (b : ℂ))
      (by simpa using hb)).norm

end AnalyticNumberTheory.Dirichlet
