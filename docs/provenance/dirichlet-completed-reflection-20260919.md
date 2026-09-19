# Dirichlet completed-L reflection provenance audit

Date: 2026-09-19

Consumer: `UyNewNas/liouville-reflection-lean`, quarter-line contour seam `Re s = 1/4` reflected to `Re(1-s)=3/4` under actual Dirichlet GRH.

## External-first search

Pinned Mathlib is `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.  It already provides the primitive completed Dirichlet-L functional equation in `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean::DirichletCharacter.IsPrimitive.completedLFunction_one_sub`, the completed/L/gamma-factor identities and differentiability, Fourier transform facts for primitive characters, and generic `Complex.logDeriv` product/composition rules.  It does not package the ordinary-L reflected logarithmic-derivative identity needed by the consumer.

Exact-same-pin source:

- repository: `subfish-zhou/liu-wang-ternary-goldbach-lean`
- commit: `b57b7307810c37267e47110d8b5f920e3e681c81`
- audited modules:
  - `BombieriVinogradov/Helpers/DirichletCharacter/PrimitiveInverseFacts.lean`
  - `BombieriVinogradov/Helpers/DirichletCharacter/PrimitiveGaussSumNonvanishing.lean`
  - `BombieriVinogradov/Helpers/DirichletCharacter/PrimitiveRootNumberNonvanishing.lean`
  - `BombieriVinogradov/Proof/SiegelWalfisz/ZeroFree/CompletedNormalization.lean`
  - `.../CompletedFunctionalEquation.lean`
  - `.../CompletedLogDerivativeReflection.lean`
  - `.../NormalizationLogDerivative.lean`
  - `.../CompletedRegularLogDerivative.lean`
  - `.../LFunctionLeftLineReflection.lean`

The source's final `logDeriv_LFunction_left_line_eq_reflected` is specialized to `Re s=-1/2` and imports `LFunctionZeroLowerStrip` solely to prove ordinary-L nonvanishing on that unconditional left line.  It is therefore not a direct theorem for the GRH quarter-line consumer.  Its completed-functional-equation and regular-point algebra are reusable without that lower-strip hierarchy.

`anthropics/formal-math@fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` (zeta23) contains the same standard completed-L reflection mechanism, e.g. `Zeta23/ThmE/CountByIntegralChi.lean::completedLSym_one_sub`, but is on a different Mathlib revision and is not a drop-in dependency.

## Minimal extraction

`AnalyticNumberTheory/Dirichlet/CompletedReflection.lean` is a provenance-preserving adaptation of the same-pin source.  It keeps only project-neutral statements and removes the Siegel--Walfisz lower-strip zero classification.  The key public theorem is

`AnalyticNumberTheory.Dirichlet.logDeriv_LFunction_eq_reflected_of_regular`.

Its hypotheses explicitly require:

- a nonprincipal primitive character;
- nonvanishing of the ordinary L-function at `s` and `1-s` for the inverse character;
- nonvanishing and differentiability of the corresponding gamma factors.

The theorem then gives the exact reflected identity

`L'/L(s,chi) = -log N - L'/L(1-s,chi⁻¹) - Gamma'/Gamma(1-s,chi⁻¹) - Gamma'/Gamma(s,chi)`.

No GRH, zero-free region, contour, Perron, Liouville defect, or application-specific parameter appears in ANT.  LR is expected to discharge the two ordinary-L nonvanishing hypotheses from its genuine Dirichlet-GRH premise at `Re s=1/4` and `3/4`, while positive-real-part Mathlib gamma-factor lemmas discharge the gamma regularity hypotheses.

## Verification status

This document records source/API equivalence and intended reuse.  Kernel/build/axiom status is determined only by exact-head GitHub CI; until that succeeds the extraction is not a verified consumer anchor.
