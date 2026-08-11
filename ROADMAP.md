# Formal Mathematics Atlas roadmap

This repository is the reusable **Prime Distribution / Analytic Number Theory**
foundation. It is upstream of theorem-focused repositories such as Chen and
future Goldbach developments.

```text
analytic-number-theory-lean
├── prime distribution (PNT and effective psi estimates)
├── Mertens II and canonical product asymptotics
└── Abelian constant-identification bridge
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
- [x] **Mertens II:** prove the reciprocal-prime sum estimate from the PNT
  facade plus partial/Abel summation, including a natural-number API.
- [x] **Canonical Mertens product:** build the convergent quadratic correction
  and derive the `O(1 / log² x)` Euler-product estimate from Mertens II.
- [x] Add the finite logarithmic product bridge; the limiting correction and
  its Euler--Mascheroni constant identification remain separate milestones.
- [x] Define the zero-extended logarithmic correction and prove its absolute
  convergence to the canonical correction constant.
- [x] Bound the correction tail by `2 / x` using the integral test.
- [x] Derive the Mertens product logarithm with its canonical constant and
  `O(1 / log x)` error; identifying that constant with Euler's constant is
  still a separate Abelian bridge.
- [x] Establish the normalized zeta--von Mangoldt bridge at `s = 1`.
- [x] Specialize the Euler-log expansion to real parameters and split it into
  the prime Dirichlet term plus the convergent correction.
- [x] Prove the scaled logarithmic Gamma kernel giving `-γ`.
- [x] Prove the Abel/Mellin representation of the prime Dirichlet sum for
  every positive displacement `ε > 0`.
- [x] Perform the logarithmic change of variables to the exponential Abel
  kernel and prove a generic `O(1/u)` remainder-vanishing theorem.
- [x] Prove that the prime finite-part limit implies the required constant
  identity via the normalized zeta limit.
- [ ] Prove the Abelian finite-part limit and conclude
  `mertensSecondConstant + logarithmicCorrectionLimit = γ`.
- [ ] Add namespace-level compatibility lemmas relating the generic finite
  objects to downstream definitions.

### v0.3 — downstream migration

- [x] Replace Chen's local PNT placeholder with the public natural-number PNT.
- [x] Replace Chen's Mertens-II placeholder with the generic theorem.
- [ ] Replace Chen's product-formula placeholder with the generic theorem.
- [ ] Keep sieve notation and Chen-specific consequences in
  `chen-theorem-lean`; move only mathematically reusable results here.

## Boundary rule

A declaration belongs here when its statement is useful without importing a
particular sieve or target theorem. Definitions tied to Chen's singular series,
sieve weights, or final theorem remain in the Chen repository.
