# Analytic Number Theory for Lean

A reusable Lean foundation for prime distribution and its analytic
consequences.

The foundation currently provides:

- a medium-strength error estimate for Chebyshev's psi function;
- quantitative Chebyshev-theta interfaces, retaining the standard square-root
  prime-power correction and exposing an `O(x / log x)` form for partial
  summation, plus its Abel-endpoint error;
- the standard prime-counting asymptotic `pi(x) ~ x / log x`;
- a natural-number prime-counting interface for downstream theorem projects.
- elementary finite prime sums/products and logarithmic estimates that form
  the neutral starting point for reusable Mertens theorems.
- an Abel-summation identity expressing reciprocal-prime sums through
  Chebyshev's theta function, including its positive-kernel form, exact
  identity main term, and a natural-number Mertens-II estimate with
  `O(1 / log x)` error.
- Mertens' product formula with exact constant `exp (-gamma) / log x` and
  `O(1 / log^2 x)` error, including a uniform natural-number interface;
- the audited zeta/Euler-log, Abel/Mellin, scaled Gamma-kernel, and finite-part
  chain identifying the canonical product constant with Euler's constant.
- the reusable sieve layer, including the Goldbach local density
  `ν(d) = 1/φ(d)` on squarefree moduli, generic Selberg main-term identities,
  and the **weighted Pan--Bombieri--Vinogradov input**: the uniform
  `3^{ω(d)}`-weighted distribution condition consumed by additive sieve
  proofs, its lcm-pair weight origin, the `errSum` seam, and the precise
  classical Pan mean-value statement as an explicitly-marked open target.

Chen-specific sieve consequences remain in `chen-theorem-lean`.

The lower-sieve error interface is under a source-faithfulness audit:
[`COMPACT_SUPPORT_LOWER_SIEVE_AUDIT.md`](COMPACT_SUPPORT_LOWER_SIEVE_AUDIT.md)
records why a compactly supported lower coefficient sequence must retain its
own `errSum`, rather than be widened to the all-divisor `errSum(1)`, before a
Chen/Pan consumer is formalized.

A second audit, [`SIEVE_MAIN_TERM_NORMALIZATION_AUDIT.md`](SIEVE_MAIN_TERM_NORMALIZATION_AUDIT.md),
records that the working `x/log x` definition is not an admissible
arbitrary-log-saving distribution main term; the genuine `Li` normalization
must be introduced before a Chen/Pan error theorem can be claimed.

For the actual Chen lower-sieve consumer, [`A1_WEIGHTED_BV_SOURCE_MATCH.md`](A1_WEIGHTED_BV_SOURCE_MATCH.md)
records the narrower, source-matched `a = 1` weighted BV supply. It separates
that theorem from the unsuitable generic Pan principal-part chain, and lists
the three remaining independent supplies: the modulus-one `pi-Li` bound,
signed MainB correction, and compact lower-sieve coefficients.

[`PNT_TO_PI_LI_WRITTEN_PROOF.md`](PNT_TO_PI_LI_WRITTEN_PROOF.md) gives the
paper derivation of that modulus-one `pi-Li` bound from ANT's existing medium
PNT and exact partial-summation identities; it is the next reusable API seam.

## Status and trust

This repository is under development. A commit is release-ready only when its
CI passes all three gates:

- every tracked Lean source is free of executable `sorry` and `admit` tokens;
- both `PrimeNumberTheoremAnd` and `AnalyticNumberTheory` build successfully;
- the declarations listed in `Audit.lean` do not depend on `sorryAx`.

Passing the audit does not mean that Lean uses no axioms. The standard mathlib
foundation (`propext`, `Classical.choice`, and `Quot.sound`) is allowed and is
reported by `#print axioms`. CI status, rather than this README, is the source
of truth for the current commit.

## Public API

Downstream projects should use:

```lean
import AnalyticNumberTheory
```

Lake dependency:

```toml
[[require]]
name = "analytic_number_theory"
git = "https://github.com/UyNewNas/analytic-number-theory-lean.git"
rev = "v0.1.0"
```

The `PrimeNumberTheoremAnd` namespace is retained as a provenance-preserving
implementation layer and is not the stable API.

## Build and audit

```sh
lake build PrimeNumberTheoremAnd AnalyticNumberTheory
lake env lean Audit.lean
```

For a release, run the same source scan as CI in addition to these commands.
The repository policy applies to every tracked `.lean` file, including root
modules and audit files.

See `UPSTREAM.md` for the exact source revision and port boundary.
