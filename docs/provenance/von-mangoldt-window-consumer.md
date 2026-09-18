# Dyadic prime / von-Mangoldt consumer slice provenance

Date: 2026-09-18.

## Consumer need

`UyNewNas/liouville-reflection-lean` currently imports the neutral finite bridge from an earlier verified ANT integration lane: dyadic prime windows, logarithmic prime-weight removal, higher-prime-power removal, and the identity expressing the dyadic von-Mangoldt character sum as a difference of two cumulative endpoint sums.

After LR was repinned to ANT `main` at `2345ff94cf3cb8de6dd79bcb75480979dc2deba9`, those four neutral modules were no longer present on `main`, even though the LR branch still imports them. This integration slice restores only that actual downstream dependency surface; it does not restore the old large `reuse/dirichlet-core-20260916` branch wholesale.

## Reuse / prior-art audit

The exact source declarations were already present and build/audit verified on ANT commit `68aca08dad78a599c29d60b3c27b6bb2ce04ab09` from `reuse/dirichlet-core-20260916`, whose PR #76 records workflow `35258007903` as fully green with the standard axiom whitelist `propext`, `Classical.choice`, `Quot.sound`.

Relevant source files from that verified anchor:

- `AnalyticNumberTheory/PrimeDistribution/DyadicPrimeWindow.lean`;
- `AnalyticNumberTheory/Dirichlet/PrimeWindowWeights.lean`;
- `AnalyticNumberTheory/Dirichlet/VonMangoldtWindow.lean`;
- `AnalyticNumberTheory/Dirichlet/VonMangoldtPartialSums.lean`.

Pinned mathlib already supplies the Chebyshev `ψ-θ` estimate used for the higher-prime-power mass and the Dirichlet-character norm bound. ANT already supplies `Dirichlet.Moments`, which owns `characterSumOn` / `weightedCharacterSumOn`, and `PrimeDistribution.PrimeNumberTheorem` for the coarse dyadic-window cardinality lower bound. No new prime number theorem, GRH theorem, zero-count theorem, Perron inversion, or application-specific Liouville result is introduced here.

The same-pin Liu--Wang explicit-Perron source remains the provenance source for ANT's separate Perron layers, but these finite window lemmas do not need to vendor another Perron or centered-Perron implementation. In particular, the old `VonMangoldtWindow.lean` import of `VonMangoldtLSeries` was dependency-only and unused by its declarations; this integration drops that import rather than reintroducing a duplicate logarithmic-derivative API already superseded on current ANT `main` by `TwistedMangoldtPerron` and the existing Dirichlet analytic modules.

## Scope decision

This is a minimal main-compatible reuse of an already verified neutral slice. The larger PR #76 remains open/diverged and is not merged, force-pushed, or treated as current main. LR should only repin to this slice after this branch itself passes a fresh build and focused axiom audit against current ANT `main`.
