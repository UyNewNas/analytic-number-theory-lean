import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic

open scoped BigOperators
open Classical

namespace AnalyticNumberTheory
namespace Dirichlet

noncomputable section

/-- Complex numbers contain a primitive root of unity of every nonzero order. -/
theorem complexHasEnoughRootsOfUnity (n : ℕ) (hn : n ≠ 0) :
    HasEnoughRootsOfUnity ℂ n := by
  classical
  haveI : NeZero n := ⟨hn⟩
  refine { prim := ?_, cyc := ?_ }
  · exact ⟨Complex.exp (2 * Real.pi * Complex.I / (n : ℂ)),
      Complex.isPrimitiveRoot_exp n hn⟩
  · infer_instance

/-- A unit-modulus complex number has conjugate equal to its inverse. -/
theorem conj_eq_inv_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    star z = z⁻¹ := by
  have hsq : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hmul : z * star z = 1 := by
    have h := Complex.mul_conj z
    rw [hsq] at h
    simpa using h
  have hne : z ≠ 0 := by
    intro hz0
    have : ‖z‖ = 0 := by simp [hz0]
    linarith
  calc
    star z = 1 * star z := by rw [one_mul]
    _ = (z⁻¹ * z) * star z := by rw [inv_mul_cancel₀ hne]
    _ = z⁻¹ * (z * star z) := by ring
    _ = z⁻¹ := by rw [hmul, mul_one]

/-- A Dirichlet character maps ring inversion of a unit to inversion of its value. -/
theorem char_apply_ringInverse
    {q : ℕ} (χ : DirichletCharacter ℂ q) {a : ZMod q} (ha : IsUnit a) :
    χ (Ring.inverse a) = (χ a)⁻¹ := by
  have hspec : (↑ha.unit : ZMod q) = a := ha.unit_spec
  have hrinv : Ring.inverse a = (↑ha.unit⁻¹ : ZMod q) := by
    calc
      Ring.inverse a = Ring.inverse (↑ha.unit : ZMod q) := by rw [hspec]
      _ = (↑ha.unit⁻¹ : ZMod q) := Ring.inverse_unit ha.unit
  rw [hrinv]
  have hmul : χ (↑ha.unit : ZMod q) * χ (↑ha.unit⁻¹ : ZMod q) = 1 := by
    rw [← map_mul χ]
    have hunit : (↑ha.unit : ZMod q) * (↑ha.unit⁻¹ : ZMod q) = 1 := by
      exact Units.val_inv ha.unit
    rw [hunit, χ.map_one]
  have hmu : χ (↑ha.unit⁻¹ : ZMod q) = (χ (↑ha.unit : ZMod q))⁻¹ := by
    exact eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hmul)
  rwa [hspec] at hmu

/-- Conjugating a Dirichlet-character value at a unit is evaluation at the ring inverse. -/
theorem star_char_eq_char_ringInverse
    {q : ℕ} (χ : DirichletCharacter ℂ q) {a : ZMod q} (ha : IsUnit a) :
    star (χ a) = χ (Ring.inverse a) := by
  have hnorm : ‖χ a‖ = 1 := DirichletCharacter.unit_norm_eq_one χ ha.unit
  calc
    star (χ a) = (χ a)⁻¹ := conj_eq_inv_of_norm_eq_one hnorm
    _ = χ (Ring.inverse a) := (char_apply_ringInverse χ ha).symm

/-- On units, mathlib's total ring inverse agrees with the native inverse in `ZMod`. -/
theorem ringInverse_eq_inv {q : ℕ} {a : ZMod q} (ha : IsUnit a) :
    Ring.inverse a = a⁻¹ := by
  calc
    Ring.inverse a = (↑ha.unit⁻¹ : ZMod q) := Ring.inverse_of_isUnit ha
    _ = ((↑ha.unit : ZMod q)⁻¹) := Units.val_inv_eq_inv_val ha.unit
    _ = a⁻¹ := by rw [ha.unit_spec]

/-- Dirichlet-character orthogonality in conjugated form on unit residue classes. -/
theorem charOrthSumUnit
    {q : ℕ} (hq : 0 < q) {a b : ZMod q} (ha : IsUnit a) (hb : IsUnit b) :
    (∑ χ : DirichletCharacter ℂ q, χ a * star (χ b)) =
      if a = b then (q.totient : ℂ) else 0 := by
  classical
  haveI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ) :=
    complexHasEnoughRootsOfUnity (Monoid.exponent (ZMod q)ˣ)
      (Monoid.exponent_ne_zero_of_finite (G := (ZMod q)ˣ))
  have hsum := DirichletCharacter.sum_char_inv_mul_char_eq ℂ (a := b) hb a
  have hrinv : Ring.inverse b = b⁻¹ := ringInverse_eq_inv hb
  calc
    (∑ χ : DirichletCharacter ℂ q, χ a * star (χ b)) =
        ∑ χ : DirichletCharacter ℂ q, χ (Ring.inverse b) * χ a := by
          apply Finset.sum_congr rfl
          intro χ _hχ
          rw [star_char_eq_char_ringInverse χ hb]
          ring
    _ = if b = a then (q.totient : ℂ) else 0 := by
      simpa [hrinv] using hsum
    _ = if a = b then (q.totient : ℂ) else 0 := by
      by_cases hab : a = b
      · simp [hab]
      · have hba : b ≠ a := by exact fun h => hab h.symm
        simp [hab, hba]

/-- Three-factor character kernel obtained from multiplicativity and orthogonality. -/
theorem charOrthMulKernel
    {q : ℕ} (hq : 0 < q) {a b c : ZMod q}
    (ha : IsUnit a) (hb : IsUnit b) (hc : IsUnit c) :
    (∑ χ : DirichletCharacter ℂ q, χ a * χ b * star (χ c)) =
      if a * b = c then (q.totient : ℂ) else 0 := by
  have hab : IsUnit (a * b) := ha.mul hb
  calc
    (∑ χ : DirichletCharacter ℂ q, χ a * χ b * star (χ c)) =
        ∑ χ : DirichletCharacter ℂ q, χ (a * b) * star (χ c) := by
          apply Finset.sum_congr rfl
          intro χ _hχ
          rw [map_mul]
    _ = if a * b = c then (q.totient : ℂ) else 0 :=
      charOrthSumUnit hq hab hc

/-- Prime-modulus natural-number specialization of the three-factor kernel. -/
theorem charOrthMulKernel_prime
    {N p n m : ℕ} (hN : N.Prime)
    (hp0 : 0 < p) (hpN : p < N)
    (hn0 : 0 < n) (hnN : n < N)
    (hm0 : 0 < m) (hmN : m < N) :
    (∑ χ : DirichletCharacter ℂ N,
      χ (p : ZMod N) * χ (n : ZMod N) * star (χ (m : ZMod N))) =
      if p * n ≡ m [MOD N] then ((N - 1 : ℕ) : ℂ) else 0 := by
  have hpunit : IsUnit (p : ZMod N) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hN).2
      (Nat.not_dvd_of_pos_of_lt hp0 hpN)).symm
  have hnunit : IsUnit (n : ZMod N) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hN).2
      (Nat.not_dvd_of_pos_of_lt hn0 hnN)).symm
  have hmunit : IsUnit (m : ZMod N) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd hN).2
      (Nat.not_dvd_of_pos_of_lt hm0 hmN)).symm
  have hiff :
      (p : ZMod N) * (n : ZMod N) = (m : ZMod N) ↔ p * n ≡ m [MOD N] := by
    simpa only [Nat.cast_mul] using (ZMod.natCast_eq_natCast_iff (p * n) m N)
  rw [charOrthMulKernel hN.pos hpunit hnunit hmunit, Nat.totient_prime hN]
  by_cases hmod : p * n ≡ m [MOD N]
  · rw [if_pos (hiff.mpr hmod), if_pos hmod]
  · rw [if_neg (fun h => hmod (hiff.mp h)), if_neg hmod]

end
end Dirichlet
end AnalyticNumberTheory
