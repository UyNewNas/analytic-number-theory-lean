# Formal Mathematics Atlas roadmap

This repository is the reusable **Prime Distribution / Analytic Number Theory**
foundation. It is upstream of theorem-focused repositories such as Chen and
future Goldbach developments.

```text
analytic-number-theory-lean
├── prime distribution (PNT and effective psi estimates)
├── finite Mertens infrastructure
└── future asymptotic Mertens theorems
        │
        ├──> chen-theorem-lean (sieve consumer)
        ├──> goldbach-lean (future)
        └──> other prime-distribution consumers
```

## Release lines

### v0.1 — prime-distribution foundation

- [x] Pin the Chen-compatible Lean/mathlib toolchain.
- [x] Port and provenance-record the minimal PNTAnd import closure.
- [x] Expose Chebyshev-psi and prime-counting PNT interfaces.
- [x] Transfer the effective psi estimate to theta, with its explicit
  square-root prime-power correction and an `O(x / log x)` partial-summation
  facade.
- [x] Provide a natural-number facade used by Chen.
- [x] Add elementary finite prime sums, products, positivity, monotonicity, and
  logarithmic-factor estimates.
- [x] Enforce zero executable `sorry`/`admit`, full builds, and an axiom audit
  in CI.

### v0.2 — reusable Mertens layer

The two independent work lines below may proceed in parallel after agreeing on
the common asymptotic/error-term API.

- [x] Establish the finite Abel-summation bridge from reciprocal-prime sums
  to Chebyshev theta.
- [x] Separate the exact `log log x` main term and the endpoint error of that
  bridge.
- [x] Add the generic improper-integral tail estimate for the
  `1 / (x log² x)` kernel.
- [x] Prove local integrability and integrable asymptotic domination of the
  Chebyshev-theta error kernel.
- [x] Define the generic Mertens-II constant and identify finite error
  integrals with their improper tails.
- [x] Derive the exact Mertens-II error decomposition and the error-kernel
  tail rate.
- [ ] **Mertens II:** prove the reciprocal-prime sum estimate, preferably from
  the PNT facade plus partial/Abel summation.
- [ ] **Mertens product:** build the convergent quadratic correction and derive
  the Euler-product estimate from Mertens II and `Mertens.Basic`.
- [ ] Add namespace-level compatibility lemmas relating the generic finite
  objects to downstream definitions.

### v0.3 — downstream migration

- [x] Replace Chen's local PNT placeholder with the public natural-number PNT.
- [ ] Replace Chen's Mertens-II placeholder with the generic theorem.
- [ ] Replace Chen's product-formula placeholder with the generic theorem.
- [ ] Keep sieve notation and Chen-specific consequences in
  `chen-theorem-lean`; move only mathematically reusable results here.

## Boundary rule

A declaration belongs here when its statement is useful without importing a
particular sieve or target theorem. Definitions tied to Chen's singular series,
sieve weights, or final theorem remain in the Chen repository.
