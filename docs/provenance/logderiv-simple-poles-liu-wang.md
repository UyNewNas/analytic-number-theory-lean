# Dirichlet logarithmic-derivative simple-pole provenance

## Named consumer

`UyNewNas/liouville-reflection-lean` PR #20 now factors its dyadic endpoint-difference
Perron integrand as

```text
-logDeriv(χ.L) * (P^s * ((2^s - 1) / s)).
```

ANT PR #102 supplies the removable quotient.  The next project-neutral seam is therefore
the at-most-simple pole statement for `logDeriv χ.LFunction`; the Mangerel-specific
dyadic assembly remains downstream.

## External-first audit — 2026-09-19

ANT remains pinned to Mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

Pinned Mathlib already supplies the Dirichlet L-function differentiability and
right-half-plane nonvanishing used to prove finite meromorphic order.  ANT's bundled
`PrimeNumberTheoremAnd.RectangleArgumentPrinciple` supplies the generic theorem
`logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top`.  No second generic
argument-principle or logarithmic-derivative pole framework is introduced here.

Exact same-pin source inspected:

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
  `hasSimplePolesOn_logDeriv_LFunction`.

The Liu--Wang theorem is strictly more appropriate than migrating its larger origin
regularization hierarchy: it applies to the logarithmic derivative itself on every
set and contains no endpoint kernel, contour geometry, zero count, GRH hypothesis,
or application parameter.

Additional overlap checks:

- current ANT `main@79ce488028ab2af17908aee0ee25eb41e6eb1f1e` contains the generic
  logarithmic-derivative residue atoms and the actual Dirichlet single-zero residue,
  but code search found no packaged `meromorphicOrderAt_LFunction_ne_top` or
  `hasSimplePolesOn_logDeriv_LFunction`;
- historical ANT `integration/dirichlet-logderiv-20260917` was inspected: its
  `FiniteRectangleLogDerivative.lean` is a quantitative zero-free rectangle bound,
  not this global finite-order/simple-pole API;
- historical `reuse/logderiv-residue-20260918` contains the already-integrated residue
  layer, not a competing simple-pole declaration;
- exact-name / `HasSimplePolesOn logDeriv` searches in canonical
  `subfish-zhou/goldbach-lean` and `anthropics/formal-math` returned no competing
  packaged declaration.  This is not a novelty claim; the implementation is an
  explicit reuse/source adaptation of Liu--Wang and the generic PNT helper.

## Adaptation decision

Source-adapt only the four neutral declarations into
`AnalyticNumberTheory.Dirichlet.LogDerivativeSimplePoles`, preserving the Liu--Wang
proof shape and attribution.  Do not migrate `IntegrandSimpleAwayZero`, regularized
origin integrands, boundary nonvanishing, residue-sum assembly, or `Centered` Perron
machinery in this slice.

`AuditLogDerivativeSimplePoles.lean` is the focused trust probe.  The dedicated
workflow requires exactly four theorem axiom reports and accepts only `propext`,
`Classical.choice`, and `Quot.sound`.
