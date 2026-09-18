# Dirichlet explicit-formula boundary-pole reuse

Date audited: 2026-09-19.

## Named consumer

The immediate consumer is `UyNewNas/liouville-reflection-lean` PR #20. Its
fixed-height sharp-dyadic contour is pinned to stable ANT and reuses ANT's
origin-cancelled dyadic simple-pole theorem. The remaining residue-theorem
obligation is boundary pole exclusion; it should not be rebuilt as a
Liouville-specific theorem when the underlying statement is project-neutral.

## External-first source audit

ANT pins Mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

The selected exact-same-pin source is
`subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`:

- `BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Residue/Poles/OriginalPoleZero.lean`,
  blob `f8ae1f7ff5e9be93aea90db5ed40870898cb8c12`, theorem
  `LFunction_eq_zero_of_explicitFormulaIntegrand_pole`;
- `BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Residue/Poles/BoundaryDisjoint.lean`,
  blob `639ce521d3ac280cee9253939d2326876eed3a9a`, theorem
  `disjoint_explicitFormulaIntegrand_poles_boundary_of_LFunction_ne_zero`;
- `BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Residue/Origin/RegularizedBoundaryPoles.lean`,
  blob `e7901936c8cec3665745150f4b1c3a78c291de91`, theorem
  `disjoint_regularizedExplicitFormulaIntegrand_poles_boundary`.

The first theorem says that, away from the separate Perron-kernel point `0`, a
pole of the unregularized nonprincipal Dirichlet explicit-formula integrand
forces a genuine zero of the Dirichlet `L`-function. The second theorem turns
border avoidance of `0` plus pointwise `L`-function nonvanishing on the border
into the `Disjoint` hypothesis consumed by the existing rectangle residue
theorem. The third transfers a single-endpoint boundary result to Liu--Wang's
heavier origin-regularized integrand and still assumes that the border avoids
`0`.

Canonical same-revision `subfish-zhou/goldbach-lean` and canonical
`anthropics/formal-math` / zeta23 were searched again on 2026-09-19 for
`explicitFormulaDyadicIntegrand`, rectangle-border pole disjointness, and a
Dirichlet-L nonvanishing-to-pole-exclusion wrapper. No competing same-shaped
packaged dyadic declaration was found. zeta23 remains broader prior art for
character contour, good-height, and zero machinery on a different Mathlib
revision; importing that hierarchy is not justified by this consumer.

Pinned Mathlib supplies the analytic-order primitives used by the proof
(`meromorphicOrderAt_mul`, analytic/nonnegative-order facts, set disjointness),
but no Dirichlet explicit-formula specialization. The dyadic kernel and its
nonnegative meromorphic order, including at the origin, are already integrated
and verified in ANT's `ExplicitFormulaDyadicOrigin` slice.

## Reuse decision

The original two Liu--Wang declarations remain provenance-preserving namespace
adaptations in `AnalyticNumberTheory.Dirichlet`.

For the actual named consumer, add only the thin dyadic corollaries:

- `LFunction_eq_zero_of_explicitFormulaDyadicIntegrand_pole`;
- `disjoint_explicitFormulaDyadicIntegrand_poles_boundary_of_LFunction_ne_zero`.

These are not claimed as a new analytic theorem. They compose ANT's already
verified factorization

`explicitFormulaDyadicIntegrand = -(L'/L) * explicitFormulaDyadicOriginKernel`

with the established nonnegative meromorphic order of the dyadic kernel.
Consequently, if the dyadic integrand has a pole at any point (including
`0`), the logarithmic derivative must have negative order there; if the
Dirichlet L-function were nonzero there, the logarithmic derivative would be
analytic, a contradiction. The border-disjointness theorem therefore needs
only pointwise L-function nonvanishing and no separate `0 ∉ border` premise.

This directly matches the downstream sharp-dyadic receiver and avoids forcing
it back through endpoint-by-endpoint pole hypotheses whose Perron kernels have
a separate origin singularity.

Do **not** migrate the Liu--Wang good-height/zero-free hierarchy, regularized
single-endpoint residue tree, zero-count machinery, GRH consequences, or any
Mangerel/Liouville parameters. The downstream project remains responsible for
proving the actual border L-function nonvanishing condition at its chosen
contour height.

This is provenance-preserving reuse plus a minimal compatibility corollary, not
a novelty claim.
