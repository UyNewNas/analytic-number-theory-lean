# Dyadic explicit-formula origin cancellation provenance

## Consumer and scope

The named consumer is `UyNewNas/liouville-reflection-lean` PR #20. Its fixed-height
Mangerel contour uses the sharp dyadic interval `(P,2P]`, hence the actual analytic
object is the endpoint difference rather than either unregularized endpoint in
isolation.

The reusable factorization is

```text
F_{2P}(s) - F_P(s)
 = - (L'/L)(s) * P^s * ((2^s - 1) / s).
```

The rightmost quotient is removable at `s = 0`. This module now carries the
project-neutral pole-order consequence as well: for positive `P` the dyadic
kernel has nonnegative meromorphic order at every point, so for a nonprincipal
Dirichlet character the complete dyadic integrand has at most simple poles on
any set. It still does not assert a contour residue theorem, boundary
zero-freeness, zero count, GRH estimate, or any Liouville/Mangerel conclusion.

## External-first audit — 2026-09-19

Pinned Mathlib revision:
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

Same-pin Liu--Wang source inspected at
`subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`:

- `.../Residue/Origin/KernelDifference.lean` packages
  `originCpowDifferenceQuotient`, its meromorphicity, punctured limit at zero,
  and nonnegative meromorphic order at zero;
- `.../Residue/Poles/LogDerivativeSimple.lean` proves that the logarithmic
  derivative of a nonprincipal Dirichlet L-function has at most simple poles;
- `LiuWang/Proof/NonSymmetricContour/Kernel.lean` contains the same order
  bookkeeping used here: `meromorphicOrderAt_mul` combines a log-derivative
  order bound `>= -1` with a meromorphic cofactor of nonnegative order;
- `.../Residue/Poles/IntegrandSimpleAwayZero.lean` gives the corresponding
  single-endpoint theorem away from zero, where the Perron kernel is analytic
  and nonvanishing;
- the larger origin-regularized single-endpoint hierarchy remains unnecessary
  for the dyadic consumer and is not migrated wholesale.

ANT PR #104 separately source-adapted the neutral nonprincipal Dirichlet-L
finite-order/simple-pole chain from the same source and was exact-head verified
before merge. The dyadic assembly reuses that API rather than reproducing it.

Searches in canonical `subfish-zhou/goldbach-lean` and
`anthropics/formal-math` / zeta23 found related explicit-formula, contour, and
zero machinery but no competing same-pinned packaged theorem for this exact
dyadic endpoint-difference simple-pole statement. This is a provenance and
reuse statement, not a novelty claim.

## Reuse decision

Keep the public dyadic surface bounded to:

- `explicitFormulaDyadicIntegrand`;
- `explicitFormulaDyadicOriginKernel`;
- exact endpoint-difference factorization;
- global meromorphicity of the positive-`P` dyadic kernel;
- nonnegative meromorphic order of that kernel at the origin and globally;
- `hasSimplePolesOn_explicitFormulaDyadicIntegrand` for nonprincipal characters.

The quotient facts are reused from ANT PR #102, the factorization/origin facts
from ANT PR #103, and the logarithmic-derivative simple-pole input from ANT PR
#104. No GRH, zero-count, contour sum, residue identification, or downstream
Liouville theorem enters this layer.

`AuditExplicitFormulaDyadicOrigin.lean` prints axioms for five theorem
statements. The dedicated workflow requires exactly five reports and accepts
only `propext`, `Classical.choice`, and `Quot.sound`.
