# Finite-height clearance reuse audit

Date: 2026-09-19

## Consumer and scope

Immediate named consumer: `UyNewNas/liouville-reflection-lean` PR #20. Its current sharp-dyadic contour reduction has reached a source-shaped selected-height receiver: the remaining analytic seam is to choose one common `T' in [T,T+1]` separated from finitely many positive/negative zero ordinates strongly enough to retain the `1/T'` horizontal decay and feed a quantitative `L'/L` bound.

The first ANT extraction in this file supplied only qualitative finite-height clearance. The current follow-up remains project-neutral but adds the exact finite-cardinality separation lemma used by the Liu--Wang two-sided selector. It still contains no Dirichlet character, `LFunction`, zero count, GRH premise, contour, Perron theorem, or application constant.

## Exact environment

Current ANT base for the quantitative follow-up:

- `main@25526048e8c59809eac1f3f8dd28460133184a30`;
- pinned Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

The external source below uses the same Mathlib pin.

## Exact-same-pin sources

Repository / commit:

- `subfish-zhou/liu-wang-ternary-goldbach-lean`;
- `b57b7307810c37267e47110d8b5f920e3e681c81`;
- license: Apache-2.0.

Qualitative source already integrated earlier:

- `LiuWang/Proof/DirichletZeroCount/Applications/ClosedHeight.lean`;
- theorem `finite_height_clearance`;
- source blob `c327d3d5be1e9ac47aa7626fe4ae4765468a0d32`.

Quantitative source for this follow-up:

- `BombieriVinogradov/Helpers/RealAnalysis/FiniteSetIntervalAvoidance.lean`;
- theorem `BombieriVinogradov.RealAnalysis.exists_unitInterval_away_from_finset`;
- source blob `2df92dcf0cd3d9eba6f9e54cfdf60a2ca22f0ed8`.

The theorem is purely finite combinatorics. For any `s : Finset Real` and any real `T`, it selects `t in [T,T+1]` with

`1 / (2 * (s.card + 2)) <= |t-x|`

for every `x` in `s`. The proof uses an interior grid with `s.card+1` points and `Fintype.exists_ne_map_eq_of_card_lt`; no analytic object appears.

This is exactly the generic core used later by the source's `TwoSidedZeroHeightSelection.lean`. That later module forms a union of positive zero ordinates and negated negative zero ordinates, bounds its cardinality by the two source zero-window counts, and then applies this finite-set theorem. The subsequent `GoodTwoSidedZeroHeight.lean` and `GoodTwoSidedHeightLogDerivativeBound.lean` add genuine zero-count and local-log-derivative analysis.

ANT therefore adapts only the finite real-set theorem as
`AnalyticNumberTheory.Analysis.existsUnitIntervalAwayFromFinset`. The existing declarations
`finiteHeightClearance` and `existsHeightAvoidingFiniteImaginaryParts` remain unchanged.

## External de-duplication

Before extending the API, current pinned ANT was checked first: it already contains the qualitative `FiniteHeightClearance` slice but no cardinality-explicit unit-interval separation theorem. Pinned Mathlib provides the finite pigeonhole primitive used by the source (`Fintype.exists_ne_map_eq_of_card_lt`) but no same-shaped packaged theorem was found. Canonical `subfish-zhou/goldbach-lean` and different-revision zeta23/formal-math were also checked; neither provides a better same-pin neutral packaged replacement for this exact seam.

The new theorem is therefore a minimal source adaptation over existing Mathlib primitives, not a second zero-selection theory.

## Integration boundary

The larger Liu--Wang source hierarchy is deliberately not copied into ANT:

- no `SymmetricCompletedZeroIndex`;
- no `zeroHeightWindow`;
- no zero-window count bound;
- no quantitative `LFunction` nonvanishing;
- no local completed-zero sum or `L'/L` theorem;
- no application-specific selected-height constants.

The intended downstream next step is smaller than the previously audited bulk extraction: LR can form finite positive/negative critical-zero ordinate sets from its already-formalized actual-GRH unit windows, use this neutral cardinality-explicit selector, and separately discharge the cardinality-to-logarithmic-scale inequality from its existing Jensen multiplicity bounds. Only the still-missing analytic `L'/L`-from-separation seam needs further source/API audit.

## Verification boundary

The module is already imported by the public `AnalyticNumberTheory` root. `AuditFiniteHeightClearance.lean` now fixes the trust surface at three declarations, including `existsUnitIntervalAwayFromFinset`. The dedicated workflow still rejects executable `sorry` / `admit` in the slice and permits only the repository's existing axiom whitelist:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

No build or axiom-audit success is claimed until GitHub Actions executes successfully on the exact PR head.
