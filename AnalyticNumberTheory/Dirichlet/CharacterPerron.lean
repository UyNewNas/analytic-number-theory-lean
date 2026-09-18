import AnalyticNumberTheory.Analysis.PerronDyadic
import AnalyticNumberTheory.Dirichlet.TwistedMangoldtPerron

/-!
# Sharp character Perron wrapper

A minimal project-neutral adapter from the exact-same-pin generic dyadic Perron
majorant to actual Mathlib Dirichlet characters.  The endpoint is kept as the
direct finite twisted von Mangoldt sum; no `characterChebyshevSum`, Vaughan
endpoint hierarchy, GRH, zero-count, or downstream application statement is
introduced here.

This is a bounded provenance-preserving adaptation of the relevant neutral part
of `LiuWang/Proof/ExplicitPerron/Characters.lean` from
`subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`.
-/

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace AnalyticNumberTheory.Dirichlet

/-- The direct finite twisted von Mangoldt endpoint used by the sharp character
Perron theorem. -/
def twistedMangoldtPartialSum {q : ℕ}
    (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, twistedMangoldtSequence χ n

/-- The Perron integrand for the logarithmic derivative of an actual Dirichlet
`LFunction`. -/
def characterPerronIntegrand {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (x : ℝ) (s : ℂ) : ℂ :=
  (-logDeriv χ.LFunction s) * ((x : ℂ) ^ s / s)

/-- On the half-plane of absolute convergence, the actual-character integrand is
exactly the generic coefficient-sequence Perron integrand. -/
theorem characterPerronIntegrand_eq_series
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ)
    {s : ℂ} (hs : 1 < s.re) :
    characterPerronIntegrand χ x s =
      LiuWang.Proof.ExplicitPerron.seriesIntegrand
        (twistedMangoldtSequence χ) x s := by
  rw [characterPerronIntegrand, LiuWang.Proof.ExplicitPerron.seriesIntegrand,
    neg_logDeriv_LFunction_eq_twistedMangoldtLSeries χ hs]

/-- The finite vertical Perron integral for an actual character is the generic
vertical integral of its twisted von Mangoldt coefficients. -/
theorem characterPerronVertical_eq_series
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ)
    {b : ℝ} (hb : 1 < b) (lo hi : ℝ) :
    LiuWang.Proof.ExplicitPerron.vertical (characterPerronIntegrand χ x) b lo hi =
      LiuWang.Proof.ExplicitPerron.vertical
        (LiuWang.Proof.ExplicitPerron.seriesIntegrand
          (twistedMangoldtSequence χ) x) b lo hi := by
  unfold LiuWang.Proof.ExplicitPerron.vertical
  congr 2
  funext u
  exact characterPerronIntegrand_eq_series χ x (by simpa using hb)

/-- Sharp finite-height Perron error for an actual Dirichlet character, with a
direct finite endpoint sum and explicit central cost.  This is the minimal
character wrapper around the already-integrated generic dyadic Perron theorem. -/
theorem norm_characterPerron_sub_partialSum_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x b T : ℝ}
    (hx : 0 < x) (hxn : ∀ n : ℕ, x ≠ n) (hb : 1 < b) (hT : 0 < T) :
    ‖LiuWang.Proof.ExplicitPerron.vertical
        (characterPerronIntegrand χ x) b (-T) T -
      twistedMangoldtPartialSum χ x‖ ≤
      (x ^ b / Real.log 2 *
          ((Real.log 4 + 4) * b / (b - 1)) +
        LiuWang.Proof.ExplicitPerron.centralCost
          (twistedMangoldtSequence χ) x b) /
        (Real.pi * T) := by
  rw [characterPerronVertical_eq_series χ x hb, twistedMangoldtPartialSum]
  apply (LiuWang.Proof.ExplicitPerron.norm_vertical_sub_sum_le_dyadic
    (twistedMangoldtSequence χ) hx hxn (zero_lt_one.trans hb) hT
    (twistedMangoldt_summable χ (by simpa using hb))).trans
  gcongr
  exact twistedMangoldt_normSum_le χ hb

end AnalyticNumberTheory.Dirichlet
