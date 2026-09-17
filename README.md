# Analytic Number Theory for Lean

A reusable Lean foundation for prime distribution, sieve infrastructure, and analytic number theory.

## Direction — 2026-09-17

ANT is maintained as a **demand-driven reusable foundation**. It is not an active second implementation of Chen's theorem. Completed application work remains downstream, while project-neutral lemmas are brought back only when a named consumer needs an exact interface.

The historical Chen line is preserved in [UyNewNas/chen-theorem-lean](https://github.com/UyNewNas/chen-theorem-lean). A completed downstream application exists in [subfish-zhou/goldbach-lean](https://github.com/subfish-zhou/goldbach-lean), which records provenance from both upstream projects. ANT reuses selected neutral results from that project without importing the Goldbach application layer wholesale.

The current work register is [Issue #1](https://github.com/UyNewNas/analytic-number-theory-lean/issues/1). It supersedes the old assumption that every historical Pan/Chen branch must be completed.

## Integrated maintenance baseline

The 2026-09 integration sprint reconciled the long-lived `dev` work back into `main` through bounded, exact-head-audited slices:

- Bombieri–Davenport baseline repair (#73);
- genuine logarithmic-integral API and neutral `pi-Li` error slice (#70);
- V1/V3 LCM-weight proof de-duplication with public compatibility wrappers (#75);
- bounded restoration of the later main Pan/Bombieri interfaces (#79–#81);
- public `#print axioms` parser reconciliation (#82);
- clean combined-tree reconciliation (#83).

PR #83's exact head `32e538c6c3ce386f25751b874a24da905a5b5540` passed the ordinary build/trust workflow and focused reconciliation audit before integration. The default branch enforces linear history, so the final integration was performed through the PR as a squash commit `ba74a8771eb34c21fccf9c6230dca71ff943bb2b`. Its Git tree is exactly the same tree that passed the PR-head checks.

The public audit registry is fixed at **463 reports** under the unchanged whitelist `propext`, `Classical.choice`, `Quot.sound`; the genuine-Li focused gate remains a separate 10-report check. Exact CI runs, not this README, are the authority for a particular commit's verification status.

## Existing foundation

- Prime distribution: Chebyshev/PNT interfaces, prime counting, genuine logarithmic-integral normalization, and quantitative prime-distribution utilities.
- Mertens: finite prime sums/products, Abel summation, Mertens II, the Mertens product, and constant-identification infrastructure.
- Sieve foundations: local density, Selberg identities/bounds, large-sieve/Bombieri–Davenport infrastructure, Pan helper layers, and neutral LCM-weight bounds.
- Dirichlet/character infrastructure is being extracted only where concrete consumers require reusable interfaces.

The general Pan/BV interfaces remain distinct from source-specific estimates used in downstream applications. A completed special-purpose application is not automatically evidence for a stronger general ANT theorem.

## External-first reuse rule

Before adding a nontrivial analytic-number-theory API, check current Mathlib and existing formalizations first. In particular:

- [subfish-zhou/goldbach-lean](https://github.com/subfish-zhou/goldbach-lean) already contains substantial Dirichlet-L / smoothed-Perron infrastructure used as a provenance-preserving extraction source;
- the canonical Anthropic [formal-math](https://github.com/anthropics/formal-math) `zeta23/` project contains Dirichlet-character zero-count, logarithmic-derivative partial-fraction, good-height, contour, and explicit-formula machinery.

If an external result has the needed type, prefer reuse or a minimal neutral adaptation. If the Lean/Mathlib revisions differ, audit the source API and recompile the extracted neutral statement against ANT's pinned environment. Do not create a parallel Perron, zero-count, or effective `L'/L` framework merely because the code lives in another repository.

## Active reusable lane

[PR #76](https://github.com/UyNewNas/analytic-number-theory-lean/pull/76) is a separate consumer-driven lane for project-neutral Dirichlet/GRH, character-moment, prime-window, von-Mangoldt partial-sum, and selected `-L'/L`/Perron interfaces used by `UyNewNas/liouville-reflection-lean`.

Because that PR has a long evolving history, it is **not** intended for wholesale merge. Stable consumer-backed blocks should be reconciled against current `dev`/`main` and independently re-audited. Application-specific Liouville/Mangerel statements remain downstream.

## Public API

```lean
import AnalyticNumberTheory
```

Consumers should pin a tested tag or commit of
`https://github.com/UyNewNas/analytic-number-theory-lean.git` in their Lake configuration. `PrimeNumberTheoremAnd` remains the provenance-preserving implementation layer; `AnalyticNumberTheory` is the public facade.

## Build and audit

```sh
lake build PrimeNumberTheoremAnd AnalyticNumberTheory
lake env lean Audit.lean
```

Use the pinned toolchain and dependencies. Releases and integration heads must pass the executable-placeholder scan, full Lean build, and declaration axiom audit. Do not use `sorry`/`admit`, custom axioms, or weaker audit gates to obtain a green build.

See [UPSTREAM.md](UPSTREAM.md) for the PNTAnd port boundary, [ROADMAP.md](ROADMAP.md) for current maintenance policy, and [LICENSE](LICENSE) for Apache-2.0 licensing. Reused downstream material must retain both its downstream provenance and any original upstream notices.
