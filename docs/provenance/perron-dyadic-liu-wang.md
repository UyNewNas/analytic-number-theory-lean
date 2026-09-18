# Dyadic Perron provenance

This ANT slice is a bounded reuse/adaptation of the project-neutral dyadic finite-height Perron majorant from:

- repository: `subfish-zhou/liu-wang-ternary-goldbach-lean`;
- exact revision: `b57b7307810c37267e47110d8b5f920e3e681c81`;
- source file: `LiuWang/Proof/ExplicitPerron/Dyadic.lean`;
- source blob: `fec5f1c1c365fa0b0c2715a80e77ad2e26b8c308`;
- Mathlib revision: the same ANT pin, `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

## External-first audit

Before integration, the following were refreshed:

- pinned Mathlib: the source needs only the already-integrated generic Perron-series layer plus `Mathlib.NumberTheory.Harmonic.Bounds` and ordinary floor/log/finite-sum APIs;
- canonical Goldbach `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`: no packaged theorem matching `norm_vertical_sub_sum_le_dyadic` / `centralCost` was found;
- canonical zeta23 `anthropics/formal-math@fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`: contains stronger but differently organized Perron/explicit-formula infrastructure on another Mathlib revision, not this same-pin generic dyadic coefficient-sequence bound;
- global GitHub code search for `norm_vertical_sub_sum_le_dyadic` found the exact Liu--Wang implementation and its downstream consumers, but no independent competing implementation.

The dependency closure is small and already available in ANT after #94:

`Dyadic.lean -> LiuWang.Proof.ExplicitPerron.Series -> integrated scalar Perron + pinned Mathlib`, plus `Mathlib.NumberTheory.Harmonic.Bounds`.

No actual Dirichlet character, GRH, zero-count theorem, von Mangoldt specialization, Mangerel constant, or full explicit-formula contour assembly is included here. Those remain separate consumers.

## Reuse policy

The source mathematical file is kept under its original module path and namespace. ANT adds only a stable import facade `AnalyticNumberTheory.Analysis.PerronDyadic` and a focused axiom audit. This avoids inventing a duplicate wrapper theorem family and preserves source provenance.
