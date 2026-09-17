import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Primitive characters at prime modulus

This file records the project-neutral fact that a Dirichlet character at prime
level is primitive exactly when it is nonprincipal.

External source audit:
`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`,
`MathlibNt/AnalyticNumberTheory/Chen1973/Chen1973Lemma4CharacterSum.lean`,
`chen1973_isPrimitive_iff_ne_one_of_odd_prime`.

The source theorem carries an `Odd p` parameter for the Chen application, but
its proof does not use it.  The neutral statement below keeps only primality.
It is proved from mathlib's conductor API and does not depend on any Liouville
application objects.
-/

noncomputable section

namespace AnalyticNumberTheory
namespace Dirichlet

/-- At prime modulus, a Dirichlet character is primitive iff it is nonprincipal. -/
theorem isPrimitive_iff_ne_one_of_prime
    {p : ℕ} (hp : p.Prime) (χ : DirichletCharacter ℂ p) :
    χ.IsPrimitive ↔ χ ≠ 1 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  constructor
  · intro hχ hχone
    have hc : χ.conductor = p := hχ
    rw [hχone, DirichletCharacter.conductor_one] at hc
    exact hp.ne_one hc.symm
  · intro hχ
    have hd : χ.conductor ∣ p := χ.conductor_dvd_level
    have hc : χ.conductor = 1 ∨ χ.conductor = p := (Nat.dvd_prime hp).mp hd
    rcases hc with hc | hc
    · exact False.elim
        (hχ ((DirichletCharacter.eq_one_iff_conductor_eq_one).2 hc))
    · exact hc

/-- One-way form convenient for analytic theorems requiring primitive characters. -/
theorem isPrimitive_of_ne_one_of_prime
    {p : ℕ} (hp : p.Prime) {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    χ.IsPrimitive :=
  (isPrimitive_iff_ne_one_of_prime hp χ).2 hχ

end Dirichlet
end AnalyticNumberTheory
