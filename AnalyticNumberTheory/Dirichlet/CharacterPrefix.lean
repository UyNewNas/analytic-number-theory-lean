import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Algebra.BigOperators.Module

/-!
# Finite prefix sums and Abel summation for Dirichlet characters

Project-neutral finite identities for complex Dirichlet characters.  These are
used by conditional Dirichlet-series arguments in the half-plane `0 < re s`.

The proofs are adapted, with provenance retained, from
`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`,
`MathlibNt/AnalyticNumberTheory/DirichletL/DirichletLWeakStripDerivative.lean`.
The source and ANT use the same pinned mathlib revision
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
-/

open Complex Finset

namespace AnalyticNumberTheory.Dirichlet

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
/-- Every complex Dirichlet-character value has norm at most one. -/
lemma character_norm_le_one (χ : DirichletCharacter ℂ q) (n : ℕ) : ‖χ n‖ ≤ 1 := by
  exact DirichletCharacter.norm_le_one χ (n : ZMod q)

/-- A nonprincipal Dirichlet character sums to zero over one complete period. -/
lemma sum_one_period_eq_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∑ n ∈ range q, χ n = 0 := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q =>
      rw [← Fin.sum_univ_eq_sum_range]
      calc
        ∑ i : Fin (q + 1), χ (i : ℕ) =
            ∑ i : Fin (q + 1), χ ((ZMod.finEquiv (q + 1)) i) := by
          apply Finset.sum_congr rfl
          intro i _
          congr 1
          apply ZMod.val_injective
          rw [ZMod.val_natCast_of_lt i.isLt]
          rfl
        _ = ∑ a : ZMod (q + 1), χ a :=
          Equiv.sum_comp (ZMod.finEquiv (q + 1)).toEquiv χ
        _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ

/-- A complete period remains zero after translation by a multiple of the modulus. -/
lemma sum_aligned_period_eq_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (k : ℕ) :
    ∑ i ∈ range q, χ (k * q + i) = 0 := by
  have hterm (i : ℕ) : χ (k * q + i) = χ i := by
    simp only [ZMod.natCast_self, mul_zero, zero_add]
  simpa only [hterm] using sum_one_period_eq_zero χ hχ

/-- Any integer number of complete periods has zero character sum. -/
lemma sum_mul_period_eq_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∀ k : ℕ, ∑ i ∈ range (k * q), χ i = 0 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, sum_range_add, ih, zero_add]
      simpa [Nat.add_comm] using sum_aligned_period_eq_zero χ hχ k

/-- Every prefix sum of a nonprincipal character is bounded by the modulus. -/
lemma norm_sum_range_character_le_modulus
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ range N, χ n‖ ≤ q := by
  have hq : 0 < q := NeZero.pos q
  have hN : N = (N / q) * q + N % q := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod N q).symm
  rw [hN, sum_range_add, sum_mul_period_eq_zero χ hχ, zero_add]
  have hshift (i : ℕ) : χ (((N / q) * q + i : ℕ)) = χ i := by
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
  simp_rw [hshift]
  calc
    ‖∑ i ∈ range (N % q), χ i‖ ≤ ∑ i ∈ range (N % q), ‖χ i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ range (N % q), (1 : ℝ) :=
      sum_le_sum fun i _ => character_norm_le_one χ i
    _ = ((N % q : ℕ) : ℝ) := by simp
    _ ≤ q := by exact_mod_cast (Nat.le_of_lt (Nat.mod_lt N hq))

omit [NeZero q] in
/-- Finite Abel summation for a Dirichlet character. -/
lemma abel_Ico (χ : DirichletCharacter ℂ q) (f : ℕ → ℂ) {m n : ℕ} (hmn : m < n) :
    ∑ i ∈ Ico m n, f i * χ i =
      f (n - 1) * (∑ i ∈ range n, χ i) - f m * (∑ i ∈ range m, χ i) -
        ∑ i ∈ Ico m (n - 1), (f (i + 1) - f i) * (∑ j ∈ range (i + 1), χ j) := by
  simpa only [smul_eq_mul] using Finset.sum_Ico_by_parts f (fun i : ℕ => χ i) hmn

end AnalyticNumberTheory.Dirichlet
