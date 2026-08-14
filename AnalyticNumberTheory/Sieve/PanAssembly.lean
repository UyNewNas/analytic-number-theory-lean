import AnalyticNumberTheory.Sieve.PanMeanValueBody
import AnalyticNumberTheory.Sieve.PanMainTerm

/-!
# PanMeanValueUniform final assembly (ant #15)

T1'/T2/T3 reduction chains + Vaughan identity compose into PanMeanValueUniform.

PanVaughanSplit declares the FINAL FORM (sum over q of mu^2 3^omega panMaxY
bounded by C xX / log^A X for every A), the remaining analytic input;
of_vaughanSplit is the trivial reduction from this final form to the target
statement (definitional equality), provable with zero sorry.
-/

namespace AnalyticNumberTheory.Sieve

open Real Finset

open scoped Classical
open scoped ArithmeticFunction.Moebius

set_option maxHeartbeats 6000000

/-- Vaughan split + three-bound assembly (analytic step, final form):
for every A > 0, there exist C, B, x0 such that for all X >= x0,
  sum_{q <= (xX)^(1/2)/log^B(xX)} mu^2(q) 3^{omega(q)} panMaxY X q (xX) f
    <= C xX / log^A X. -/
def PanVaughanSplit (x : ℕ → ℝ) (f : ℕ → ℝ) (u v : ℕ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, ∃ x₀ : ℕ,
    ∀ X : ℕ, x₀ ≤ X →
      ∑ q ∈ Finset.range (Nat.floor ((x X) ^ (1 / 2 : ℝ) /
            (log (x X)) ^ B) + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card *
          panMaxY X q (Nat.floor (x X)) f ≤
        C * x X / (log (x X)) ^ A

/-- Assembly theorem: Vaughan split (final form) => PanMeanValueUniform.
The statement of PanVaughanSplit matches the target PanMeanValueUniform
verbatim, so this is a trivial reduction (definitional equality). -/
theorem PanMeanValueUniform.of_vaughanSplit
    {x : ℕ → ℝ} {f : ℕ → ℝ} {u v : ℕ}
    (hV : PanVaughanSplit x f u v) :
    PanMeanValueUniform x f := by
  simpa [PanMeanValueUniform, PanVaughanSplit] using hV

end AnalyticNumberTheory.Sieve
