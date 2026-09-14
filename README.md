# Analytic Number Theory for Lean

A reusable Lean foundation for prime distribution and its analytic consequences.

## Direction — 2026-09-14

The project is maintained as a reusable foundation, with **demand-driven fixes
and selective reuse of completed downstream work**. Its purpose is no longer to
supply a second independently completed Chen proof.

[subfish-zhou/goldbach-lean](https://github.com/subfish-zhou/goldbach-lean) has
completed Chen and Li–Liu applications on foundations originating here and in
[chen-theorem-lean](https://github.com/UyNewNas/chen-theorem-lean). Its
[provenance record](https://github.com/subfish-zhou/goldbach-lean/blob/df1f3b3b721c9a0b5e38ba39d5c0e3c2a1d72f59/docs/PROVENANCE.md)
credits both upstream repositories and describes subsequent downstream proof
completion and engineering. It currently includes an adapted local source
closure rather than depending on this repository as an external Lake package.

The [current roadmap](ROADMAP.md) and [work register (#1)](https://github.com/UyNewNas/analytic-number-theory-lean/issues/1)
replace the old assumption that every open Pan/Chen branch must be completed.
The first bounded comparison is the genuine logarithmic-integral API in
[#69](https://github.com/UyNewNas/analytic-number-theory-lean/issues/69), reusing
existing [PR #70](https://github.com/UyNewNas/analytic-number-theory-lean/pull/70)
rather than opening a duplicate implementation.

## Existing foundation

- Prime distribution: medium-strength Chebyshev-psi error, quantitative theta
  interfaces, prime-counting asymptotics, and a natural-number PNT facade.
- Mertens: finite prime sums/products, Abel summation, Mertens II with
  `O(1 / log x)` error, and the product formula with exact constant
  `exp (-gamma)` and `O(1 / log^2 x)` error.
- Constant identification: the zeta/Euler-log, Abel/Mellin, Gamma-kernel, and
  finite-part chain connecting the canonical product constant to Euler's constant.
- Sieve foundations: local density, Selberg identities and bounds, singular
  series, and explicit distribution/weighted-Pan interfaces.

The local general Pan interfaces and their hypotheses remain distinct from the
proved source-specific estimates used by downstream Chen applications. A
completed application is not automatically a proof of every older general API.

## Reuse scope

Prefer a small, theorem-oriented extraction with a named consumer over copying
the downstream project wholesale. Preserve source revisions and attribution,
keep endpoint conventions and quantifier order explicit, and retain the existing
build and axiom checks. Results tied to a particular application's source
weights or final counting object remain with that application.

## Public API

```lean
import AnalyticNumberTheory
```

Consumers should pin a tested tag or commit of
`https://github.com/UyNewNas/analytic-number-theory-lean.git` in their Lake
configuration. The `PrimeNumberTheoremAnd` namespace is the provenance-preserving
implementation layer; the `AnalyticNumberTheory` facade is the public API.

## Build and audit

```sh
lake build PrimeNumberTheoremAnd AnalyticNumberTheory
lake env lean Audit.lean
```

Use the pinned toolchain and dependencies. A release needs a successful full
build, the existing executable-placeholder scan, and the declaration axiom
audit. Standard Lean/mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`)
remain allowed. CI for the exact commit, not this maintenance roadmap, records
its build status.

See [UPSTREAM.md](UPSTREAM.md) for the PNTAnd source revision and port boundary,
and [LICENSE](LICENSE) for Apache-2.0 licensing. Downstream contributions brought
back here must retain their own provenance as well as the original upstream
notices.
