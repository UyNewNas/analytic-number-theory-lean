import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing

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

/-- Uniform zero-free rectangle for all non-principal Dirichlet characters modulo `N`. -/
def ZeroFreeRectangle (N : ℕ) [NeZero N] (α T : ℝ) : Prop :=
  ∀ (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ s : ℂ,
    α < s.re → s.re ≤ 1 → |s.im| ≤ T →
      DirichletCharacter.LFunction χ s ≠ 0

/-- GRH plus unconditional non-vanishing on `Re(s) ≥ 1` supplies every rectangle whose
left edge lies on or to the right of the critical line. -/
theorem GRHAt.zeroFreeRectangle
    {N : ℕ} [NeZero N] (hGRH : GRHAt N)
    {α T : ℝ} (hα : (1 / 2 : ℝ) ≤ α) :
    ZeroFreeRectangle N α T := by
  intro χ hχ s hαs _hs1 _hT
  by_cases hslt : s.re < 1
  · intro hz
    have hs0 : 0 < s.re := by
      have : (0 : ℝ) < 1 / 2 := by norm_num
      linarith
    have hhalf := hGRH χ s hs0 hslt hz
    have hstrict : (1 / 2 : ℝ) < s.re := lt_of_le_of_lt hα hαs
    exact (ne_of_lt hstrict) hhalf
  · have hsge : (1 : ℝ) ≤ s.re := le_of_not_gt hslt
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) hsge

end Dirichlet
end AnalyticNumberTheory
