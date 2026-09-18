# Sieve interface status ledger

Kernel checking establishes only the exact Lean proposition. This ledger
records which currently named sieve interfaces are source-valid consumers and
which are legacy/conditional records that must not close Chen.

| interface | status | reason / replacement |
| --- | --- | --- |
| `UniformJurkatRichertMainTerm`, `UniformJurkatRichertLowerBound` | legacy, not source-valid Chen input | use `D/z` and all-divisor error; replace by supported JR at `log D/log z` |
| `WeightedPanCondition` at `x/log x` main mass | legacy, false for arbitrary log saving | migrate to genuine `Li` and supported `a=1` theorem |
| generic `PanMeanValueUniform -> WeightedPanCondition` bridge | unavailable for Chen lower consumer | generic principal part has wrong size; use `WeightedBVAtOne` for delta weight |
| fixed-parameter `bombieri_vinogradov` | finite existential remainder only | not an averaged BV theorem; cannot supply a level-of-distribution consumer |
| compact supported lower-sieve finite inequality | valid finite algebra | waits for corrected JR coefficient/main-term supply and true-Li remainder |
| `chebyshevPsi_medium_error` / theta transfer / `pi_asymp_aux` | valid reusable input | written proof specifies future quantitative `pi-Li` facade |

The corresponding Chen ledger is:

| Chen consumer | status | required replacement |
| --- | --- | --- |
| `ChenWeightedPanInput` / `CorrectedChenDistributionCondition` | legacy under old normalization and all divisors | supported lower-sieve error split: `d=1` PNT-Li, `2≤d≤D` WeightedBVAtOne, signed MainB |
| `CorrectedChenPanTruncationInput` | legacy all-divisor repair route | compact support removes its artificial tail; no absolute lcm expansion |
| `q1APErrorUniformBound` | open dimension-two switching remainder | true Li plus source-matched signed/repackaged lcm theorem |
| `CorrectedChenOmegaUpperBound` | open Chen-local analytic supply | variable-a prime-pair / dimension-two sieve and q1 worklines |

Consequently, `#print axioms` entries for a legacy proposition are evidence
only that its definition is kernel-clean; they are not evidence that its
analytic hypotheses are true or that it may be used in the final theorem.
