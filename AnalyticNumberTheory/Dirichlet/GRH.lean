import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace AnalyticNumberTheory
namespace Dirichlet

/-- GRH at one nonzero modulus, stated directly for mathlib's analytically continued
Dirichlet `LFunction`. Only zeros in the open critical strip are constrained. -/
def GRHAt (N : ℕ) [NeZero N] : Prop :=
  ∀ (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 →
      s.re = 1 / 2

/-- Generalized Riemann hypothesis for all Dirichlet L-functions. -/
def GRH : Prop :=
  ∀ (N : ℕ) (hN : N ≠ 0), @GRHAt N ⟨hN⟩

/-- The global Dirichlet GRH premise specializes to every concrete nonzero modulus. -/
theorem GRH.at (h : GRH) {N : ℕ} [NeZero N] : GRHAt N := by
  exact h N (NeZero.ne N)

/-- Equivalent zero-free formulation away from the critical line in the open critical strip. -/
theorem grhAt_iff (N : ℕ) [NeZero N] :
    GRHAt N ↔
      ∀ (χ : DirichletCharacter ℂ N) (s : ℂ),
        0 < s.re → s.re < 1 → s.re ≠ 1 / 2 →
          DirichletCharacter.LFunction χ s ≠ 0 := by
  constructor
  · intro h χ s hs0 hs1 hhalf hzero
    exact hhalf (h χ s hs0 hs1 hzero)
  · intro h χ s hs0 hs1 hzero
    by_contra hhalf
    exact h χ s hs0 hs1 hhalf hzero

end Dirichlet
end AnalyticNumberTheory
