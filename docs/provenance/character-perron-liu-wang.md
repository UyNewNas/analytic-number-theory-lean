# Sharp character Perron wrapper provenance

Date: 2026-09-18; real-endpoint residue audit refreshed 2026-09-22.

## Immediate consumer and scope

This bounded ANT slice supplies project-neutral seams requested by the actual downstream consumer `UyNewNas/liouville-reflection-lean`: a finite-height Perron estimate for a genuine Mathlib Dirichlet character with the endpoint left as the direct finite twisted von Mangoldt sum, plus the local residue of that same real-endpoint Perron integrand.

It deliberately does **not** introduce `characterChebyshevSum`, Vaughan endpoint machinery, GRH, zero-counting, centered contour assembly, Mangerel constants, Liouville application statements, or a packaged explicit formula.

## External-first audit

The following anchors were checked before adding or extending this wrapper:

- ANT pinned Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`;
- canonical same-revision Goldbach: `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`;
- canonical zeta23/formal-math: `anthropics/formal-math@fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` (different Mathlib revision; broader contour/zero prior art, not a drop-in same-pin wrapper);
- exact-same-pin Liu--Wang: `subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`, especially `LiuWang/Proof/ExplicitPerron/Characters.lean` and `BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/ZeroResidue.lean`.

The Liu--Wang character file contains the direct source pattern for the real-endpoint character integrand, reduction to the generic coefficient-sequence Perron integrand, and the finite-height character estimate. Its import closure is larger than the current neutral consumer needs: it also pulls in production `characterChebyshevSum` / Vaughan endpoint support and a right-half-plane log-derivative bound.

The Liu--Wang zero-residue theorem proves the same multiplicity-weighted local residue geometry for a natural endpoint. Exact code search for `residue_characterIntegrand` / an equivalent packaged residue of the real-endpoint character Perron integrand found no competing declaration in exact-same-pin Liu--Wang, canonical Goldbach, or zeta23. ANT already has the generic logarithmic-derivative residue atom and the natural-endpoint specialization, so the 2026-09-22 extension is a one-theorem compatibility seam over the already-public `characterPerronIntegrand`, not a new contour hierarchy.

ANT already integrated the dependency-closed neutral pieces needed here:

1. exact-same-pin generic scalar/series/dyadic Perron machinery, including `LiuWang.Proof.ExplicitPerron.norm_vertical_sub_sum_le_dyadic`;
2. the minimal twisted von Mangoldt character core, including `twistedMangoldtSequence`, absolute convergence, `-L'/L = LSeries(χ·Λ)` on `Re(s)>1`, and the explicit character-uniform norm-series bound;
3. `AnalyticNumberTheory.ComplexAnalysis.LogDerivResidue` and the analytic-order bookkeeping used by `ExplicitFormulaResidue`.

Therefore this slice adapts only the thin glue between already-audited layers rather than copying the full upstream `Characters.lean` / completed-zero / explicit-formula dependency hierarchy.

## ANT declarations

`AnalyticNumberTheory/Dirichlet/CharacterPerron.lean` exports:

- `twistedMangoldtPartialSum`;
- `characterPerronIntegrand`;
- `characterPerronIntegrand_eq_series`;
- `characterPerronVertical_eq_series`;
- `norm_characterPerron_sub_partialSum_le`.

`AnalyticNumberTheory/Dirichlet/CharacterPerronResidue.lean` adds only:

- `residue_characterPerronIntegrand` for `x : ℝ`, `0 < x`, `ρ ≠ 0`, and nonprincipal `χ`, with exact residue
  `- analyticOrderNatAt χ.LFunction ρ * x^ρ / ρ`.

Keeping `x` real is the point of the extension: downstream can shift the contour at the same nonintegral endpoint used by the sharp Perron theorem and no longer needs a half-integer-to-integer vertical transport whose absolute bound grows with contour height.

## Trust boundary

`AuditCharacterPerron.lean` audits the five original declarations plus `residue_characterPerronIntegrand`. The dedicated additive workflow compiles `PrimeNumberTheoremAnd BombieriVinogradov LiuWang AnalyticNumberTheory`, requires six focused reports, and requires the existing augmented public audit plus this one new report = a fixed 575-report character-Perron augmented audit. The allowed axiom whitelist remains exactly `propext`, `Classical.choice`, `Quot.sound`.

No merge claim is made until the exact PR head receives a real root build and the focused/public axiom audits pass on that same SHA.
