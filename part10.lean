
/-! ## 9. The type-I assembly analysis (ant #15, question (a)/(b)/(c))

**Setup.** The actual consumer of the mean-value input is
`panTypeICharMeanSieveBound` (PanMeanValueBody.lean:871), via
`PanTypeICharacterMeanValue.of_sieveBound` (:903). Its L^2 intermediate
`panTypeICharSquareMeanBound` (:892) asks for
  sum_{q<=Q} mu^2 3^omega * sum_{chi mod q} ||V_chi(m)||^2 <= C (m + Q^2) S(m).
The per-modulus material already proved is `characterSieveModulus_le`
  sum_chi ||S_chi||^2 <= (phi(q)/q) * sum_{r<q} |T(r/q)|^2   (one q at a time)
together with the additive sieve `largeSieveBound(m+1, 1/q^2) = m + O(q^2 log q)`.

**(a) Can the q-summation be done from the per-q material + polylog? NO.**
The per-q bound gives the q-sum with weight mu^2 3^omega (phi(q)/q) times (m + q^2 log q).
The regrouping lemma `perModulus_regroup` shows this is exactly
  sum_{q'<=Q} W(q') * sum_{red r'} |T(r'/q')|^2,  W(q') = sum_{d<=Q/q'} mu^2 3^omega phi(q'd)/(q'd),
and the effective weight W(1) = sum_{d<=Q} mu^2 3^omega phi(d)/d ~ (log Q)^3 is UNBOUNDED
(numerics in check_perq.py: W(1) = 94, 211, 473, 1098 at Q = 40, 80, 160, 320). Equivalently,
  sum_{q<=Q} mu^2 3^omega (phi/q) (m + q^2 log q) ~ m Q (log Q)^2 + Q^3 (log Q)^3,
which is ~ Q (log Q)^3 times bigger than (m + Q^2) at m = Q^2 (ratio 704, 1664, 3844, 9777).
So the per-q stacking cannot produce the (m + Q^2) shape; moreover
`panTypeICharSquareMeanBound` itself is false (u = 1, m = Q^2; see section 7).

**(b) The real Bombieri-Davenport (all q simultaneously) is needed — and proved.**
`characterSieveModulus_le` is per-modulus (fixed q). The all-q version must
apply the additive sieve to the WHOLE Farey set X_Q = {r/q : 1 <= q <= Q, 0 <= r < q}
(which is 1/Q^2-well-spaced) with `largeSieveRationalPoints` — that is exactly
`bombieriDavenport_le` / `bombieriDavenport_vaughanFirst`
(sum over primitive chi with the (q/phi(q)) weight; the Gauss-sum inversion converts the
weighted primitive sum to the UNWEIGHTED reduced-fraction sum, and the additive sieve is
applied once, on X_Q). This gives the m + Q^2 shape (up to the weak sieve constant).

**(c) The direct-Parseval-stacking counterexample is avoided.**
The red-team note (PanMeanValueBody.lean:699-701) shows that stacking the per-q Parseval
over ALL characters (or with multiplicities on the rational points) fails. The BD proof
never does that: it (i) restricts to primitive characters, (ii) uses the Gauss-sum
inversion |S_chi|^2 = (1/q) |sum_a star(chi a) T(a/q)|^2, (iii) applies the unit-group
Parseval to get the sum over REDUCED fractions with weight 1, and (iv) applies the
additive sieve once on the Farey set. No per-q Parseval stacking occurs.

**Remaining gap to the assembly.** The proved BD lemma carries the (q/phi(q)) weight over
primitive characters; the target carries mu^2 3^omega over all characters. Bridging the
two needs the conductor decomposition (each chi mod q lifts a unique primitive chi' mod
q' | q) with the non-coprime part controlled by density estimates, and then the
mu^2 3^omega weight assembly (sub-steps S2-S3 of section 7). The sharp (m + Q^2)
constant additionally needs the N + delta^{-1} additive-sieve constant (sub-step S4).
-/
