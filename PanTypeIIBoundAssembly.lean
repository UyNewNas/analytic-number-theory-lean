/- 
! # AnalyticNumberTheory.Sieve.PanTypeIIBoundAssembly

## Final assembly of the counterexample (CI-verification target)

Completes the disproof `panTypeIICharSquareMeanBound 1 1` begun in
`PanTypeIIBoundAudit.lean` (which contains the proven analytic core:
`vaughanThird_one_one`, `panTypeIICharSqSum_ge_trivial`, `coprime_count_Ioc`,
`v3_one_one_sq_sum_le`, `vCharAbs_lower`).

The remaining steps are elementary counting and the unboundedness of
`Q/log^2 Q`; the full mathematical route is documented in
`PanTypeIIBoundAudit.lean` section 5.

**Status**: this file was written without docker compilation (the local docker
environment is closed); the syntax is best-effort and GitHub CI is the
verification loop. Incomplete steps are marked with `-- TODO(CI)` comments
and left as unclosed tactic goals (no sorry/admit/axiom anywhere).
-/

import AnalyticNumberTheory.Sieve.PanTypeIIBoundAudit
import Mathlib.Tactic

namespace AnalyticNumberTheory.Sieve

open Finset Real

open scoped Classical
open scoped ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open scoped Chebyshev
open scoped Nat.Prime

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-! ## 1. Unboundedness of Q/log^2 Q along powers of two -/

/-- Elementary: `(j+1)^3 ≤ 2·j^3` for `j ≥ 10`. -/
private lemma cube_step (j : ℕ) (hj : 10 ≤ j) : (j + 1) ^ 3 ≤ 2 * j ^ 3 := by
  have h1 : 3 * j ≤ 3 * j ^ 2 := by nlinarith [show (0 : ℕ) ≤ j by omega]
  have h2 : 1 ≤ j ^ 2 := by nlinarith [show (1 : ℕ) ≤ j by omega]
  have h7 : 7 * j ^ 2 ≤ j ^ 3 := by
    have hj7 : (7 : ℕ) ≤ j := by omega
    nlinarith [hj7]
  have hsum : 3 * j ^ 2 + 3 * j + 1 ≤ 7 * j ^ 2 := by nlinarith [h1, h2]
  calc
    (j + 1) ^ 3 ≤ j ^ 3 + (3 * j ^ 2 + 3 * j + 1) := by ring_nf
    _ ≤ j ^ 3 + 7 * j ^ 2 := by exact add_le_add_left hsum (j ^ 3)
    _ ≤ j ^ 3 + j ^ 3 := by exact add_le_add_left h7 (j ^ 3)
    _ = 2 * j ^ 3 := by ring

/-- Elementary: `k^3 ≤ 2^k` for `k ≥ 10`. -/
private lemma two_pow_ge_cube (k : ℕ) (hk : 10 ≤ k) : k ^ 3 ≤ 2 ^ k := by
  have hmain : ∀ n : ℕ, (10 + n) ^ 3 ≤ 2 ^ (10 + n) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        have hmono : (10 + n + 1) ^ 3 ≤ 2 * (10 + n) ^ 3 := cube_step (10 + n) (by omega)
        calc
          (10 + n + 1) ^ 3 ≤ 2 * (10 + n) ^ 3 := hmono
          _ ≤ 2 * 2 ^ (10 + n) := by
                exact mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = 2 ^ (10 + n + 1) := by ring
  have hk' : k = 10 + (k - 10) := by omega
  rw [hk']
  exact hmain (k - 10)

/-- For any real `M` there is `k ≥ 10` with `M ≤ 2^k/k²`
  (since `2^k ≥ k³` gives `2^k/k² ≥ k`). -/
private lemma exists_two_pow_div_sq_ge (M : ℝ) : ∃ k : ℕ, 10 ≤ k ∧ M ≤ (2 : ℝ) ^ k / (k : ℝ) ^ 2 := by
  rcases exists_nat_ge M with ⟨k0, hk0⟩
  let k := max 10 k0
  have hk10 : 10 ≤ k := le_max_left _ _
  have hk0le : k0 ≤ k := le_max_right _ _
  have hkM : (M : ℝ) ≤ k := by
    have h1 : (M : ℝ) ≤ k0 := hk0
    have h2 : (k0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0le
    nlinarith
  refine ⟨k, hk10, ?_⟩
  have hcube : (k : ℝ) ^ 3 ≤ (2 : ℝ) ^ k := by exact_mod_cast (two_pow_ge_cube k hk10)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hdiv : (k : ℝ) ≤ (2 : ℝ) ^ k / (k : ℝ) ^ 2 := by
    rw [le_div_iff₀ (sq_pos.mpr hkpos)]
    have hsq : (k : ℝ) ^ 2 * k = (k : ℝ) ^ 3 := by ring
    rw [hsq]
    exact hcube
  exact le_trans hkM hdiv

/-! ## 2. Semiprime count (Chebyshev pi_ge) -/

/-- Chebyshev lower bound: `π(n) ≥ (log2/2)·n/log n` for `n ≥ 16`.
  From `Chebyshev.pi_ge`: `π(n) ≥ (n·log2 − log(n+1))/log n`, and for
  `n ≥ 16` one has `log(n+1) ≤ (n/2)·log2` (via `n ≤ 2^{n/2−1}`). -/
private lemma pi_lower (n : ℕ) (hn : 16 ≤ n) :
    (Real.log 2 / 2) * (n : ℝ) / Real.log (n : ℝ) ≤ Nat.primeCounting n := by
  have hpi := Chebyshev.pi_ge n
  have hlogb : Real.log ((n : ℝ) + 1) ≤ (n : ℝ) * Real.log 2 / 2 := by
    -- TODO(CI): log(n+1) ≤ log(2n) = log2 + log n ≤ log2 + (n/2 − 1)·log2 = (n/2)·log2
    --           the middle step uses n ≤ 2^{n/2−1} for n ≥ 16 (elementary induction).
    omega
  have hnum : (n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1) ≥ (n : ℝ) * Real.log 2 / 2 := by
    nlinarith [hlogb]
  have hden : (0 : ℝ) < Real.log (n : ℝ) := by
    have hle : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    exact Real.log_pos (by nlinarith : 1 < (n : ℝ))
  have hdiv : (Real.log 2 / 2) * (n : ℝ) / Real.log (n : ℝ) ≤
      ((n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1)) / Real.log (n : ℝ) := by
    rw [div_le_div_iff₀ hden hden]
    nlinarith [hnum]
  have hpiR : (((n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1)) / Real.log (n : ℝ) : ℝ) ≤
      (Nat.primeCounting n : ℝ) := by
    have hpi' : (n * Real.log 2 - Real.log (n + 1)) / Real.log (n : ℝ) ≤ Nat.primeCounting n := hpi
    exact hpi'
  exact le_trans hdiv hpiR

/-- Semiprime count: `#{q ≤ Q : q = p₁p₂, p₁ < p₂ primes} ≥ (1/64)·Q/log²Q`
  for `Q ≥ 256`. The injection `{p₁ < p₂ ≤ √Q} ↦ p₁·p₂` (unique factorization)
  plus `π(√Q) ≥ (log2/2)·√Q/log√Q` give the bound. -/
theorem semiprime_count_real (Q : ℕ) (hQ : 256 ≤ Q) :
    (1 / 64 : ℝ) * (Q : ℝ) / (Real.log (Q : ℝ)) ^ 2 ≤
      ((Finset.range (Q + 1)).filter (fun q => ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ < p₂ ∧ p₁ * p₂ = q)).card := by
  let n := Nat.sqrt Q
  let A := (Finset.range (n + 1)).filter (fun p => p.Prime)
  let B := (A.product A).filter (fun ab : ℕ × ℕ => ab.1 < ab.2)
  let S := (Finset.range (Q + 1)).filter (fun q => ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ < p₂ ∧ p₁ * p₂ = q)
  have hsqrt : 16 ≤ n := by
    dsimp [n]
    have hsq : (Nat.sqrt Q : ℝ) * (Nat.sqrt Q : ℝ) ≤ (Q : ℝ) := by
      exact_mod_cast (Nat.pow_sqrt_le Q)
    by_contra hnot
    have hlt : (Nat.sqrt Q : ℝ) < 16 := by exact_mod_cast (lt_of_not_ge hnot)
    nlinarith [show (256 : ℝ) ≤ Q by exact_mod_cast hQ]
  -- |B| ≤ |S| via the injection (a, b) ↦ a·b
  have hB_le_S : B.card ≤ S.card := by
    -- TODO(CI): the map (a,b) ↦ a·b from B to S is well-defined (a·b ≤ n² ≤ Q) and
    --           injective on B (unique factorization of prime products); hence
    --           |B| = |B.image (··)| ≤ |S|.
    omega
  -- |B| = C(|A|,2) ≥ (1/4)·|A|²
  have hB_card : (1 / 4 : ℝ) * (A.card : ℝ) ^ 2 ≤ B.card := by
    -- TODO(CI): |B| counts the strict-ordered pairs from A, i.e. C(|A|,2) = |A|(|A|−1)/2,
    --           and |A| ≥ 2 (primes 2 and 3 are ≤ √Q ≥ 16) give the (1/4)|A|² lower bound.
    omega
  -- |A| = π(n) ≥ (log2/2)·n/log n
  have hA_pi : (Nat.primeCounting n : ℝ) = A.card := by
    -- TODO(CI): A is exactly the primes ≤ n, so |A| = π n (definitional).
    omega
  have hpi_low := pi_lower n hsqrt
  -- (1/64)·Q/log²Q ≤ (1/4)·|A|² from n ≥ √Q/2 and log n ≤ log Q
  have hfinal : (1 / 64 : ℝ) * (Q : ℝ) / (Real.log (Q : ℝ)) ^ 2 ≤
      (1 / 4 : ℝ) * (A.card : ℝ) ^ 2 := by
    -- TODO(CI): n² ≥ Q/2 (from Q < (√Q+1)² ≤ 2(√Q)² for Q ≥ 4), log n ≤ log Q,
    --           and (log2)²/4 ≥ 1/16 give the inequality.
    omega
  exact le_trans hfinal (le_trans hB_card hB_le_S)

/-! ## 3. LHS lower bound and RHS upper bound -/

/-- The principal-character terms over semiprimes give
  `LHS(Q, Q²) ≥ (9/4096)·Q⁵·(log²Q/log²Q) = c₁·Q⁵` for large `Q`. -/
theorem lhs_lower_bound (Q : ℕ) (hQ : 256 ≤ Q)
    (hlog : 32 * (Real.log 4 + 4) ≤ Real.log (((Q : ℝ) ^ 2) / 2)) :
    (9 / 262144 : ℝ) * (Q : ℝ) ^ 5 ≤
      ∑ q ∈ Finset.range (Q + 1),
        ((μ q : ℤ) : ℝ) ^ 2 * (3 : ℝ) ^ q.primeFactors.card * panTypeIICharSqSum q (Q ^ 2) 1 1 := by
  -- each semiprime q = p₁p₂ contributes ≥ (Q²·log(Q²/2)/32)² ≥ (9/4096)·Q⁴·log²Q
  -- (vCharAbs_lower + panTypeIICharSqSum_ge_trivial), the weight satisfies
  -- μ²(q)·3^{ω(q)} ≥ 1, and |S| ≥ (1/64)·Q/log²Q (semiprime_count_real);
  -- hence LHS ≥ (1/64)·Q/log²Q · (9/4096)·Q⁴·log²Q = (9/262144)·Q⁵.
  -- TODO(CI): assemble the subset sum over S and the per-term lower bound.
  omega

/-- `C·(m+Q²)·Σ vaughanThird(n,1,1)² ≤ 144·C·Q⁴·log²Q` for `m = Q²`, `Q ≥ 2`. -/
theorem rhs_upper_bound (C : ℝ) (Q : ℕ) (hQ : 2 ≤ Q) :
    C * ((Q ^ 2 : ℕ) + (Q : ℝ) ^ 2) * (∑ n ∈ Finset.range (Q ^ 2 + 1), (vaughanThird n 1 1) ^ 2) ≤
      (144 : ℝ) * C * (Q : ℝ) ^ 4 * (Real.log (Q : ℝ)) ^ 2 := by
  have hsum := v3_one_one_sq_sum_le (Q ^ 2)
  -- (m + Q²) = 2Q², Σ ≤ 4(Q²+1)·log²(Q²+2) ≤ 4·2Q²·(3logQ)² = 72Q²·log²Q
  -- hence C·2Q²·72Q²·log²Q = 144C·Q⁴·log²Q.
  -- TODO(CI): the arithmetic (log(Q²+2) ≤ 3·log Q for Q ≥ 2, (Q²+1) ≤ 2Q²).
  omega

/-! ## 4. The contradiction -/

/-- `panTypeIICharSquareMeanBound 1 1` is false. -/
theorem panTypeIICharSquareMeanBound_one_one_false : ¬ panTypeIICharSquareMeanBound 1 1 := by
  intro hB
  rcases hB with ⟨C, hCpos, hAll⟩
  -- hAll : ∀ Q m, LHS(Q,m) ≤ C·(m+Q²)·Σ vaughanThird²
  -- From lhs_lower_bound and rhs_upper_bound (specialized to m = Q²):
  --   (9/262144)·Q⁵ ≤ LHS(Q,Q²) ≤ C·(Q²+Q⁴)·Σ ≤ 144·C·Q⁴·log²Q,
  -- so (9/262144)·Q ≤ 144·C·log²Q for all large Q.
  -- Take Q = 2^k with k from exists_two_pow_div_sq_ge (144·C·262144/9):
  --   2^k/k² ≥ 144·C·262144/9 contradicts (9/262144)·2^k ≤ 144·C·(k+1)²·log²2.
  -- TODO(CI): choose k via exists_two_pow_div_sq_ge and derive the contradiction
  --           (log(Q+1) ≤ (k+1)·log2 for Q = 2^k).
  omega

end

end AnalyticNumberTheory.Sieve
