# Generic Perron series provenance

This bounded compatibility slice comes from:

- repository: `subfish-zhou/liu-wang-ternary-goldbach-lean`;
- source revision: `b57b7307810c37267e47110d8b5f920e3e681c81`;
- source file: `LiuWang/Proof/ExplicitPerron/Series.lean`;
- source blob: `e31986d6b43460fcfd8b08a5a228acccfc9122e5`;
- source Mathlib pin: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, exactly matching ANT.

## External-first decision

The source file imports both the neutral scalar Perron theorem and
`BombieriVinogradov...PerronSeries.Interchange`.  The latter is a
Dirichlet-character-specialized interchange theorem.  The generic
coefficient-sequence proof in `Series.lean` does not invoke that theorem; its
`vertical_eq_tsum` proof directly invokes pinned Mathlib
`intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm` after proving its
own compact sup-norm summability estimate.

Fresh searches of canonical Goldbach
`09b97db5764ade1246bfb77206baa1b124760958` and canonical zeta23/formal-math
`fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` did not find a competing packaged
generic theorem with the same API.

Therefore ANT treats this as a compatibility/adaptation problem, not a new
proof problem.

## Local adaptation

The vendored `LiuWang/Proof/ExplicitPerron/Series.lean` preserves the source
mathematical declarations and proof bodies, with one intentional dependency
change at the import boundary:

- remove the character-specialized `PerronSeries.Interchange` import;
- import `Mathlib.MeasureTheory.Integral.DominatedConvergence` directly for the
  termwise interval-integral interchange theorem;
- import `Mathlib.NumberTheory.LSeries.Basic` directly for the generic L-series
  objects used in the file;
- reuse ANT's already integrated exact-same-pin scalar `Perron.Main` slice.

The whole Liu-Wang package is still not added as a Lake dependency because it
exports colliding `AnalyticNumberTheory` / `PrimeNumberTheoremAnd` roots and a
different LeanArchitect revision.  Only this dependency-closed neutral slice
is under consideration.

## Verification boundary

PR #94 is initially a compile/audit probe.  A dedicated `LiuWang` Lake target
and `AuditPerronSeries.lean` require a real same-pin build plus four fixed axiom
reports for `vertical_eq_tsum`, `summable_majorant`, `tsum_stepTerm`, and
`norm_vertical_sub_sum_le`.  Allowed axioms remain exactly `propext`,
`Classical.choice`, and `Quot.sound`.

A green probe only establishes that the specialized import is unnecessary in
ANT's pinned environment.  Public-facade integration and any subsequent
`Dyadic` extraction remain separate decisions.