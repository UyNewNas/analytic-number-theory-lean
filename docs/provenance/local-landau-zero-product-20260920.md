# Local Landau zero-product provenance audit

Date: 2026-09-20

Consumer: `UyNewNas/liouville-reflection-lean`, selected-height central-strip logarithmic-derivative receiver.

## External-first comparison

Pinned Mathlib is `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
`Mathlib/Analysis/Calculus/LogDeriv.lean` already provides the exact generic identities needed for finite products: `logDeriv_prod`, `logDeriv_fun_pow`, and `logDeriv_apply`.  The pinned file does not package the Landau-specific finite zero polynomial statement.

Different-revision prior art:

- repository: `anthropics/formal-math`;
- commit: `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`;
- modules:
  - `zeta23/Zeta23/WeilEF/Landau.lean`, declarations `analyticAt_finset_prod_sub_pow`, `logDeriv_zero_prod`, `logDeriv_split`;
  - `zeta23/Zeta23/FromPNTPlus/StrongPNTPrefix.lean`, declarations `ZeroFactor`, `ZeroFactorization`, `Cf`, `CfAnalytic`.

The source is Apache-2.0 but is on a different Mathlib revision.  This branch therefore does not import or bulk-copy the zeta23 package.  It adapts only the two finite-product algebra lemmas directly against ANT's pinned Mathlib.

Canonical same-revision source `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958` was searched for `logDeriv_zero_prod` / finite-product `(z-rho)^m` helpers; no competing packaged statement under this interface was found.

## Existing ANT coverage

Current stable ANT `main@c5ed033f1b694b42d266b375588de7010387659b` already has the other neutral pieces that make a bounded local-Landau route plausible:

- `ComplexAnalysis/JensenZeros.lean`: `SetOfZeros`, radius monotonicity, and closed-disc finiteness;
- `ComplexAnalysis/JensenDivisorBound.lean`: multiplicity-counted Jensen bound;
- `Dirichlet/LocalLogDerivative.lean`: zero-free local logarithmic-derivative estimate;
- `Dirichlet/LFunctionGrowth.lean` and the right-half-plane anchor layer for the later Dirichlet specialization.

The old PrimeNumberTheoremAnd `ZerosBound` prefix therefore does not need to be re-ported merely to obtain zero counting.

## This extraction

`AnalyticNumberTheory/ComplexAnalysis/LocalZeroProduct.lean` currently adds only:

- `analyticAt_finsetProd_sub_pow`;
- `logDeriv_finsetProd_sub_pow`.

Both are project-neutral.  They mention no Dirichlet character, GRH, zero-count constant, contour, Perron term, or Liouville object.  The second theorem is the exact finite-product algebra needed by a future `logDeriv_split` theorem once the regularized zero-free factor has been constructed.

## Remaining dependency cut

The genuinely missing neutral work is still the regularized factor, not the finite-product derivative algebra:

1. a pinned-revision replacement for the source's `ZeroFactor` / `ZeroFactorization` interface;
2. a finite zero-product quotient that is analytic and nonvanishing across the divided-out zeros;
3. a local identity splitting `logDeriv f` into the finite zero sum plus the regular factor;
4. growth transfer for that regular factor sufficient to feed the existing `norm_logDeriv_le_small_disk` theorem.

No claim is made here that those four items are already proved.  This branch is intentionally bounded: establish and verify the algebraic prerequisite first, then port only the next missing neutral layer if exact-head CI supports it.
