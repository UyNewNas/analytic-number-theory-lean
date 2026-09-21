# Positive-half-plane digamma regularity provenance audit

Date: 2026-09-21

Named consumer: `UyNewNas/liouville-reflection-lean`, selected-height gamma compact-complement path.

## External-first search

Pinned Mathlib revision is `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

Pinned Mathlib already defines `Complex.digamma` in
`Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.lean` as `logDeriv Complex.Gamma`, proves
`Complex.meromorphic_digamma`, and provides the required Gamma primitives through
`Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean` and `Gamma.Basic`:

- `Complex.differentiableAt_Gamma` away from non-positive integer poles;
- `Complex.Gamma_ne_zero` away from those poles;
- the generic analytic/logarithmic-derivative infrastructure used below.

It does not package the exact project-facing theorem “`Complex.digamma` is analytic at every
`z` with `0 < z.re`”. Current ANT main was searched for `digamma`; no competing declaration exists.

Different-revision prior art:

- repository: `anthropics/formal-math`;
- commit: `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`;
- module: `zeta23/Zeta23/ThmE/GammaFactsChiProof.lean`;
- declaration: `Zeta23.ThmE.GammaChi.analyticAt_digamma'`.

That proof is dependency-small: it obtains differentiability of Gamma on the open right half-plane,
upgrades to analyticity, differentiates, divides by nonzero Gamma, and identifies the quotient with
digamma. No zeta23 Stirling theorem, trigamma series, zero-count theorem, or application-specific
constant enters this declaration.

Exact-same-pin prior art:

- repository: `subfish-zhou/liu-wang-ternary-goldbach-lean`;
- commit: `b57b7307810c37267e47110d8b5f920e3e681c81`.

Its gamma-factor horizontal bound is stronger quantitatively, but the reusable source stack pulls in
custom digamma-series/scaling infrastructure. Search found no independent packaged theorem under the
small `analyticAt_digamma` interface. Therefore this PR does not copy the Liu--Wang horizontal stack.

## Adaptation and scope

`AnalyticNumberTheory/ComplexAnalysis/DigammaRegularity.lean` source-adapts only the neutral theorem

`AnalyticNumberTheory.ComplexAnalysis.analyticAt_digamma_of_re_pos`.

Statement:

```lean
{z : ℂ} → 0 < z.re → AnalyticAt ℂ Complex.digamma z
```

The helper excluding Gamma poles is private. The public theorem contains no Dirichlet character,
GRH/zero-free premise, contour/Perron object, Stirling estimate, quantitative digamma bound, or
Liouville/Mangerel parameter.

This is a compatibility/reuse extraction, not a novelty claim.

## Consumer boundary

The immediate downstream use is the bounded-height branch of the selected-height gamma estimate.
LR should derive continuity on its fixed compact rectangle from this theorem, obtain an existential
finite bound by compactness, and keep parity/selected-height specialization downstream. Large-height
quantitative control remains sourced separately from the exact-same-pin Liu--Wang theorem.

Do not widen this PR into a new quantitative digamma-series/Stirling API unless an exact neutral
consumer requires it.

## Verification gate

The module is root-imported by `AnalyticNumberTheory.lean`. `AuditDigammaRegularity.lean` prints
axioms for the single public theorem, and `.github/workflows/digamma-regularity-audit.yml` rejects
executable `sorry`/`admit`, builds both the module and root target, and enforces the standard axiom
whitelist `{propext, Classical.choice, Quot.sound}`.

No downstream repin or merge should occur until the exact PR head receives a real full build/trust
verdict and this focused audit passes on the same SHA.
