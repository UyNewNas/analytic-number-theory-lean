# Dirichlet explicit-formula boundary-pole reuse

Date audited: 2026-09-19.

## Named consumer

The immediate consumer is `UyNewNas/liouville-reflection-lean` PR #20.  Its
fixed-height sharp-dyadic contour has already been repinned to ANT
`main@591bb0f4286881e48e3cb765bd58f8e9a5c79f96` and now reuses ANT's verified
origin-cancelled dyadic simple-pole theorem.  The next genuine residue-theorem
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
  `disjoint_explicitFormulaIntegrand_poles_boundary_of_LFunction_ne_zero`.

The first theorem says that, away from the separate Perron-kernel point `0`, a
pole of the unregularized nonprincipal Dirichlet explicit-formula integrand
forces a genuine zero of the Dirichlet `L`-function.  The second theorem turns
border avoidance of `0` plus pointwise `L`-function nonvanishing on the border
into the `Disjoint` hypothesis consumed by the existing rectangle residue
theorem.

Canonical same-revision `subfish-zhou/goldbach-lean` and canonical
`anthropics/formal-math` / zeta23 were searched for the same packaged theorem
names and boundary-pole seam.  No competing same-shaped packaged declaration
was found there.  zeta23 remains broader prior art for character contour and
zero machinery, on a different Mathlib revision; importing that hierarchy is
not justified by this consumer.

## Reuse decision

Source-adapt only the two neutral declarations into
`AnalyticNumberTheory.Dirichlet`, reusing ANT's existing
`explicitFormulaIntegrand`, pinned Mathlib analytic-order infrastructure, and
`PrimeNumberTheoremAnd.ResidueCalcOnRectangles` border notation.

Do **not** migrate the Liu--Wang good-height/zero-free hierarchy, regularized
single-endpoint residue tree, zero-count machinery, GRH consequences, or any
Mangerel/Liouville parameters.  The downstream project remains responsible for
proving the actual border nonvanishing condition at its chosen contour height.

This is provenance-preserving reuse / namespace adaptation, not a novelty
claim.
