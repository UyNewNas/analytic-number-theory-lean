# Quantitative local zero-quotient provenance audit

Date: 2026-09-20

Named consumer: `UyNewNas/liouville-reflection-lean` PR #20, current regular-part handoff `05ccfae49f92d77754d367f4ea5da66e494bdd72`.

## External-first comparison

Pinned Mathlib remains `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. ANT stable base for this extraction is `c6238d98312b6ae81e4ac76729d844fabd64d586`.

The closest complete prior art is:

- repository: `anthropics/formal-math`;
- commit: `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`;
- file: `zeta23/Zeta23/WeilEF/Landau.lean`;
- declaration: `norm_logDeriv_Cf_le`.

That theorem uses the same source-shaped radii: growth on `24/25`, zero removal through `22/25`, holomorphic logarithm on `17/20`, and receiver radius `83/100`. It proves the regular-part bound `44795000 * log B`. Its zero-product/Jensen/max-principle bookkeeping was audited line-by-line before this extraction. This ANT work is therefore not a novelty claim and does not infer originality from a renamed interface.

Exact-same-pin Liu--Wang and canonical Goldbach remain relevant prior art for the wider Dirichlet/explicit-formula program, but the purpose of this slice is deliberately narrower: package only the neutral regularized finite-zero quotient estimate already demanded by LR, reusing ANT's existing local quotient and local complex-analysis APIs instead of importing a second full Landau/StrongPNT hierarchy.

## Existing verified ANT seams reused

Stable ANT already provides:

- `ComplexAnalysis.jensenZeroMultiplicityBound_normalized` for the multiplicity-counted Jensen bound;
- `ComplexAnalysis.regularizedFiniteZeroQuotient`, its analyticity/nonvanishing, finite-product reconstruction, and exact `logDeriv` split;
- `Dirichlet.exists_holomorphicLog_on_ball` for a zero-free holomorphic logarithm;
- `Dirichlet.norm_deriv_le_fixed_radii_83_100`, merged in PR #115, for the exact `17/20 -> 21/25 -> 83/100` Borel--Caratheodory/Cauchy geometry with derivative coefficient `16800`.

The `c6238d98312b6ae81e4ac76729d844fabd64d586` post-merge check set contains 21 completed successful checks and no failed or still-running check, so it is a stable base for this branch.

## This bounded extraction

`AnalyticNumberTheory/ComplexAnalysis/LocalZeroQuotientBound.lean` adds one project-neutral theorem:

`AnalyticNumberTheory.ComplexAnalysis.norm_logDeriv_regularizedFiniteZeroQuotient_le`.

Under the same normalized unit-disc hypotheses as the cited source theorem, it proves the candidate coefficient

`520800 * log B`

on `||z|| <= 83/100` after dividing out zeros through `22/25`.

The arithmetic is source-shaped: the quotient oscillation coefficient is bounded by `31 * log B`, exactly as in the source argument; ANT then applies the already-verified fixed-radius derivative theorem, giving `16800 * 31 = 520800`. Thus the improvement relative to `44795000` is specifically a reuse consequence of the tighter already-verified local derivative geometry, not a change to the Jensen zero count or an additional analytic hypothesis.

No Dirichlet character, GRH premise, zero-free region, contour/Perron theorem, or Liouville/Mangerel parameter occurs in the new public statement.

## Verification boundary

At creation time this branch is **pending exact-head compilation and axiom audit**. The existing local-zero-quotient focused audit is extended from five to six declarations and its executable-placeholder scan includes the new file. `AnalyticNumberTheory.lean` root-imports the new module.

The coefficient `520800` must not be advertised as verified until the exact PR head passes the ordinary full root build/trust workflow and the focused six-declaration audit. Downstream must not repin to this branch head; only a subsequently verified stable merge SHA may be consumed.
