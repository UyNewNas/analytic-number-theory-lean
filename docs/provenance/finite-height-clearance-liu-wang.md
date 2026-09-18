# Finite-height clearance reuse audit

Date: 2026-09-19

## Consumer and scope

Immediate named consumer: `UyNewNas/liouville-reflection-lean` PR #20.  Its current sharp-dyadic contour reduction has already reduced the rectangle-border nonvanishing premise, under actual Dirichlet GRH, to excluding zeros at the two critical-line points of heights `±T`.  The remaining project-facing step is to choose a nearby height avoiding a finite set of already-proved finite critical-line zero windows.

This ANT slice is intentionally smaller: it contains only finite-set height clearance and an interval-choice corollary.  It contains no Dirichlet character, `LFunction`, zero count, GRH premise, contour, Perron theorem, or application constant.

## Exact environment

ANT base before this extraction:

- `main@6e7815c5f2afc94700d71b2c7695ac511560895d`;
- pinned Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

The external source below uses the same Mathlib pin.

## Exact-same-pin source

Primary source:

- repository: `subfish-zhou/liu-wang-ternary-goldbach-lean`;
- commit: `b57b7307810c37267e47110d8b5f920e3e681c81`;
- file: `LiuWang/Proof/DirichletZeroCount/Applications/ClosedHeight.lean`;
- source blob observed at that commit: `c327d3d5be1e9ac47aa7626fe4ae4765468a0d32`;
- license: Apache-2.0.

That file proves `finite_height_clearance` and then stronger character-uniform statements including `exists_common_regular_height`, `exists_common_count_plateau`, and `exists_complete_common_regular_height`.  Those stronger statements depend on Liu--Wang's `CompleteValues` / Dirichlet zero-count hierarchy.

ANT source-adapts only the finite combinatorial theorem as
`AnalyticNumberTheory.Analysis.finiteHeightClearance` and adds the thin corollary
`existsHeightAvoidingFiniteImaginaryParts`.  This is compatibility/reuse, not a novelty claim.

## De-duplication decision

Before writing, current pinned ANT, canonical `subfish-zhou/goldbach-lean`, and canonical `anthropics/formal-math` / zeta23 were searched for the same finite-height-clearance / regular-height package.  No same-shaped packaged neutral theorem was found in those trees.  ANT already has `ComplexAnalysis.finite_zeros_closedBall`, itself a zeta23-informed compactness adapter; that theorem establishes finiteness of analytic zeros, while the present slice starts after a finite set is available and selects a safe height.  They are complementary rather than competing APIs.

The full Liu--Wang character-uniform zero-count hierarchy is therefore not migrated.  The downstream consumer should form the finite forbidden set from its existing genuine critical-line zero-window finiteness theorems, use this neutral height selector, and keep GRH/Mangerel-specific assembly downstream.

## Verification boundary

The new module is imported by the public `AnalyticNumberTheory` root, so the ordinary full build reaches it.  `AuditFiniteHeightClearance.lean` fixes the trust surface at two declarations, and the additive workflow rejects executable `sorry` / `admit` in the slice and permits only the repository's existing axiom whitelist:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

No build or axiom-audit success is claimed until GitHub Actions executes successfully on the exact PR head.
