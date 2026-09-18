# Sharp character Perron wrapper provenance

Date: 2026-09-18.

## Immediate consumer and scope

This bounded ANT slice supplies the next project-neutral seam requested by the actual downstream consumer `UyNewNas/liouville-reflection-lean`: a finite-height Perron estimate for a genuine Mathlib Dirichlet character with the endpoint left as the direct finite twisted von Mangoldt sum.

It deliberately does **not** introduce `characterChebyshevSum`, Vaughan endpoint machinery, GRH, zero-counting, centered contour assembly, Mangerel constants, or Liouville application statements.

## External-first audit

The following anchors were checked before adding this wrapper:

- ANT pinned Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`;
- canonical same-revision Goldbach: `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`;
- canonical zeta23/formal-math: `anthropics/formal-math@fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` (different Mathlib revision; broader contour/zero prior art, not a drop-in same-pin wrapper);
- exact-same-pin Liu--Wang: `subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`, especially `LiuWang/Proof/ExplicitPerron/Characters.lean`.

The Liu--Wang file contains the direct source pattern for the character integrand, reduction to the generic coefficient-sequence Perron integrand, and the finite-height character estimate.  Its import closure is larger than the current neutral consumer needs: it also pulls in production `characterChebyshevSum` / Vaughan endpoint support and a right-half-plane log-derivative bound.

ANT already integrated the dependency-closed neutral pieces needed here:

1. exact-same-pin generic scalar/series/dyadic Perron machinery (#93--#95), including `LiuWang.Proof.ExplicitPerron.norm_vertical_sub_sum_le_dyadic`;
2. the minimal twisted von Mangoldt character core (#96), including `twistedMangoldtSequence`, absolute convergence, `-L'/L = LSeries(χ·Λ)` on `Re(s)>1`, and the explicit character-uniform norm-series bound.

Therefore this slice adapts only the thin glue between those already-audited layers rather than copying the full upstream `Characters.lean` dependency hierarchy.

## ANT declarations

`AnalyticNumberTheory/Dirichlet/CharacterPerron.lean` adds:

- `twistedMangoldtPartialSum`;
- `characterPerronIntegrand`;
- `characterPerronIntegrand_eq_series`;
- `characterPerronVertical_eq_series`;
- `norm_characterPerron_sub_partialSum_le`.

The final theorem has a direct finite endpoint sum and the existing explicit dyadic central cost.  It is reuse/adaptation of existing formalized mathematics, not a claim of a new Perron theorem.

## Trust boundary

`AuditCharacterPerron.lean` audits exactly these five declarations.  The dedicated additive workflow must compile `PrimeNumberTheoremAnd BombieriVinogradov LiuWang AnalyticNumberTheory`, require five focused reports, and require the existing 568-report twisted-Mangoldt augmented public surface plus these five reports = a fixed 573-report augmented public audit.  The allowed axiom whitelist remains exactly `propext`, `Classical.choice`, `Quot.sound`.
