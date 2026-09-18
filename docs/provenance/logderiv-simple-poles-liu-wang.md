# Dirichlet logarithmic-derivative simple-pole provenance

## Named consumer

`UyNewNas/liouville-reflection-lean` PR #20 uses the sharp dyadic endpoint-difference
Perron integrand.  ANT PR #103 now packages its neutral factorization

```text
-logDeriv(χ.L) * (P^s * ((2^s - 1) / s)).
```

The next neutral seam is therefore the at-most-simple-pole statement for
`logDeriv χ.LFunction`; the Mangerel-specific contour assembly remains downstream.

## External-first audit — 2026-09-19

ANT remains pinned to Mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

Exact same-pin Liu--Wang sources inspected:

- repository: `subfish-zhou/liu-wang-ternary-goldbach-lean`;
- commit: `b57b7307810c37267e47110d8b5f920e3e681c81`;
- `.../Residue/Meromorphic/LFunction.lean`, blob
  `7b66660a8dfdae9cf7746aabba6f18498615305f`, declaration
  `meromorphic_logDeriv_LFunction`;
- `.../Residue/Poles/LFunctionFiniteOrder.lean`, blob
  `8f28a5ff9078fc80e5ec9b7424c00a78b7fb08ea`, declarations
  `meromorphic_LFunction_of_ne_one` and `meromorphicOrderAt_LFunction_ne_top`;
- `.../Residue/Poles/LogDerivativeSimple.lean`, blob
  `0e6aa08b98d5faa1e6543e9c1bd3db77ea6f559f`, declaration
  `hasSimplePolesOn_logDeriv_LFunction`;
- `BombieriVinogradov/Helpers/ComplexAnalysis/BoundedOrder.lean`, blob
  `bdd3cc91e7db7e478b7ad292361f6e5e90d09ff8`, which records the bounded-remainder
  order lemma used by the same proof pattern.

The generic source theorem
`logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top` was also checked in
`AxiomMath/PrimeNumberTheoremAnd@75c7dffd3ddfe2bda7c33264c780a97486f8303d`,
`PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean`, and in the same-pin
Liu--Wang copy of that file.  Code search also finds the same lineage in
`AlexKontorovich/PrimeNumberTheoremAnd`; this is established prior art, not a
novel ANT result.

### Correction found by CI

The first PR head incorrectly imported
`PrimeNumberTheoremAnd.RectangleArgumentPrinciple`, assuming that file was present
in ANT's vendored `PrimeNumberTheoremAnd` subset.  Exact-head Actions disproved that
assumption: the file is not vendored here.  No theorem failure was hidden; the bad
import stopped the build before the new module compiled.

ANT already contains the hard local principal-part estimate
`AnalyticNumberTheory.ComplexAnalysis.logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt`
in `ComplexAnalysis/LogDerivResidue.lean`, source-adapted earlier from the same
lineage.  The corrected implementation therefore source-adapts only the remaining
small order-bookkeeping layer into
`ComplexAnalysis/LogDerivSimplePoles.lean`, rather than importing or copying the
whole rectangle-argument-principle file.

## Additional overlap checks

- ANT `main@d11beb848b58c5e171c4bbcd79e8d6f676301b7c` contains the generic
  logarithmic-derivative principal-part/residue atoms, the Dirichlet explicit-formula
  residue layer, the removable origin quotient, and the dyadic-origin factorization;
  it does not package the global finite-order/simple-pole theorem before this PR.
- Historical ANT `integration/dirichlet-logderiv-20260917` was inspected:
  `FiniteRectangleLogDerivative.lean` is a quantitative zero-free finite-rectangle
  bound, not this global finite-order/simple-pole API.
- Historical `reuse/logderiv-residue-20260918` contains the already-integrated local
  residue layer, not a competing packaged simple-pole declaration.
- Exact-name/shape searches in canonical `subfish-zhou/goldbach-lean` and
  `anthropics/formal-math` found no competing packaged ANT-target declaration.
  This is not a novelty claim: the implementation explicitly reuses/source-adapts
  the prior work above.

## Adaptation decision

Keep only two neutral layers:

1. `AnalyticNumberTheory.ComplexAnalysis.LogDerivSimplePoles` — one public generic
   theorem from finite meromorphic order to at-most-simple logarithmic-derivative
   poles; proof-only order helpers remain private and reuse ANT's existing
   principal-part theorem.
2. `AnalyticNumberTheory.Dirichlet.LogDerivativeSimplePoles` — four nonprincipal
   Dirichlet-L declarations culminating in `hasSimplePolesOn_logDeriv_LFunction`.

Do not migrate Liu--Wang's `IntegrandSimpleAwayZero`, full regularized-origin
integrands, residue-sum assembly, boundary nonvanishing, zero-count hierarchy,
`Centered` machinery, or downstream Mangerel/Liouville parameters in this slice.

`AuditLogDerivativeSimplePoles.lean` is the focused trust probe.  The dedicated
workflow requires exactly five theorem axiom reports and accepts only `propext`,
`Classical.choice`, and `Quot.sound`.
