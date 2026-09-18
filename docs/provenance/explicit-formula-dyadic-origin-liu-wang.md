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

The rightmost quotient is removable at `s = 0`. This module carries the
project-neutral pole-order consequence as well: for positive `P` the dyadic
kernel has nonnegative meromorphic order at every point, so for a nonprincipal
Dirichlet character the complete dyadic integrand has at most simple poles on
any set.

For the current named consumer, the remaining local seam was more precise: at a
nonzero contour pole, identify the repository's direct dyadic `residue` with the
difference of the two endpoint residues already used by the downstream critical-
window estimates.  The current branch adds exactly that local bridge.  It still
does not assert a contour-sum reindexing, boundary zero-freeness, zero count,
GRH estimate, or any Liouville/Mangerel conclusion.

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
- `.../ZeroResidue.lean` proves the single-endpoint nonzero residue formula;
- `LiuWang/Proof/NonSymmetricContour/Kernel.lean` contains the same order
  bookkeeping used here: `meromorphicOrderAt_mul` combines a log-derivative
  order bound `>= -1` with a meromorphic cofactor of nonnegative order;
- `.../Residue/Poles/IntegrandSimpleAwayZero.lean` gives the corresponding
  single-endpoint theorem away from zero;
- the larger origin-regularized single-endpoint hierarchy remains unnecessary
  for the dyadic consumer and is not migrated wholesale.

A fresh exact-name search for a packaged direct-dyadic residue theorem (including
`residue_explicitFormulaDyadicIntegrand` and a generic `residue_sub`) found no
same-shaped declaration in Liu--Wang, current ANT, canonical
`subfish-zhou/goldbach-lean`, or the checked PrimeNumberTheoremAnd copies.
Canonical `anthropics/formal-math` / zeta23 remains prior art for stronger
argument-principle and explicit-formula infrastructure on a different Mathlib
revision, but it is not a smaller same-pin drop-in for this local seam.

Accordingly the implementation reuses ANT's already-integrated generic
`logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt` and
`residue_mul_eq_of_sub_principal_isBigO_one`, plus the verified endpoint residue
formula.  It does **not** assume unrestricted algebraic linearity of the
repository's simple-pole `residue` stopgap.  The equality with endpoint-residue
subtraction is proved only after both sides are independently identified by the
same local principal-part calculation.

This is reuse/assembly and compatibility work, not a novelty claim.

## Reuse decision

Keep the public dyadic surface bounded to:

- `explicitFormulaDyadicIntegrand`;
- `explicitFormulaDyadicOriginKernel`;
- exact endpoint-difference factorization;
- global meromorphicity of the positive-`P` dyadic kernel;
- nonnegative meromorphic order of that kernel at the origin and globally;
- `hasSimplePolesOn_explicitFormulaDyadicIntegrand` for nonprincipal characters;
- the nonzero-point direct residue formula;
- the nonzero-point equality between the direct dyadic residue and the two
  already-verified endpoint residues.

The quotient facts are reused from ANT PR #102, the factorization/origin facts
from ANT PR #103, the logarithmic-derivative simple-pole input from ANT PR #104,
and the generic principal-part residue atom from ANT #92.  No GRH, zero-count,
contour sum, Mangerel parameter, or downstream Liouville theorem enters this
layer.

`AuditExplicitFormulaDyadicOrigin.lean` prints axioms for seven theorem
statements. The dedicated workflow requires exactly seven reports and accepts
only `propext`, `Classical.choice`, and `Quot.sound`.
