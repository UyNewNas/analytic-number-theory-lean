# Analytic Number Theory for Lean

A reusable Lean foundation for prime distribution and its analytic
consequences.

Version 0.1 is focused on porting the minimal PNTAnd dependency closure needed
for:

- a medium-strength error estimate for Chebyshev's psi function;
- quantitative Chebyshev-theta interfaces, retaining the standard square-root
  prime-power correction and exposing an `O(x / log x)` form for partial
  summation;
- the standard prime-counting asymptotic `pi(x) ~ x / log x`;
- a natural-number prime-counting interface for downstream theorem projects.
- elementary finite prime sums/products and logarithmic estimates that form
  the neutral starting point for reusable Mertens theorems.

The asymptotic Mertens second theorem and product formula are planned for
version 0.2. Chen-specific sieve consequences remain in `chen-theorem-lean`.

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
