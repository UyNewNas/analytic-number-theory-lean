# Local Landau zero-product provenance audit

Date: 2026-09-20

Consumer: `UyNewNas/liouville-reflection-lean`, selected-height central-strip logarithmic-derivative receiver.

## External-first comparison

Pinned Mathlib is `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
`Mathlib/Analysis/Calculus/LogDeriv.lean` already provides the exact generic identities needed for finite products: `logDeriv_prod`, `logDeriv_fun_pow`, and `logDeriv_apply`.  `Mathlib/Analysis/Analytic/Order.lean` already provides the local analytic-order factorization, and `Mathlib/Analysis/Normed/Module/Connected.lean` provides `Metric.isPreconnected_closedBall`.  Pinned Mathlib does not package the Landau-specific finite zero polynomial logarithmic-derivative statement.

Different-revision prior art:

- repository: `anthropics/formal-math`;
- commit: `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`;
- modules:
  - `zeta23/Zeta23/WeilEF/Landau.lean`, declarations `analyticAt_finset_prod_sub_pow`, `logDeriv_zero_prod`, `logDeriv_split`;
  - `zeta23/Zeta23/FromPNTPlus/StrongPNTPrefix.lean`, declarations `ZeroFactor`, `ZeroFactorization`, `Cf`, `CfAnalytic`.

The source is Apache-2.0 but is on a different Mathlib revision.  This branch therefore does not import or bulk-copy the zeta23 package.  It adapts only the bounded local factorization/finite-product algebra directly against ANT's pinned Mathlib.

Canonical same-revision source `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958` was searched for `logDeriv_zero_prod` / finite-product `(z-rho)^m` helpers; no competing packaged statement under this interface was found.

## Existing ANT coverage

Current stable ANT `main@c5ed033f1b694b42d266b375588de7010387659b` already has the other neutral pieces that make a bounded local-Landau route plausible:

- `ComplexAnalysis/JensenZeros.lean`: `SetOfZeros`, radius monotonicity, and closed-disc finiteness;
- `ComplexAnalysis/JensenDivisorBound.lean`: multiplicity-counted Jensen bound;
- `Dirichlet/LocalLogDerivative.lean`: zero-free local logarithmic-derivative estimate;
- `Dirichlet/LFunctionGrowth.lean` and the right-half-plane anchor layer for the later Dirichlet specialization.

The old PrimeNumberTheoremAnd `ZerosBound` prefix therefore does not need to be re-ported merely to obtain zero counting.

## This extraction

`AnalyticNumberTheory/ComplexAnalysis/LocalZeroProduct.lean` adds three project-neutral declarations:

- `exists_analyticFactor_at_zero`: finite local analytic order plus the canonical nonvanishing analytic factor at a zero;
- `analyticAt_finsetProd_sub_pow`;
- `logDeriv_finsetProd_sub_pow`: the exact finite zero-sum logarithmic derivative away from the listed zeros.

They mention no Dirichlet character, GRH, zero-count constant, contour, Perron term, or Liouville object.  The third theorem is the exact finite-product algebra needed by a future `logDeriv_split` theorem once the regularized zero-free factor has been constructed.

## Exact-head verification

Final code head for this slice: `503cf4865e619f7f9962865a4dcb90c0ae4fbf08` on PR #113.

Two earlier compile failures were fixed without weakening any theorem:

1. missing pinned analytic-order imports (`d2e6269577cbe01cc2bd202de2f6c1391217ffbe`);
2. topology notation scope plus the pinned namespace for `Metric.isPreconnected_closedBall` (`6093abab8ea1e3e9c1a16c7a4aa1d931f7b5188d`).

At exact head `503cf486...`:

- dedicated workflow `Local zero-product audit` run `35468853979` completed successfully: root build, placeholder rejection, and the 3-declaration axiom audit all passed;
- ordinary `Lean build and trust audit` run `35468853977` completed successfully, including root build and the repository public-theorem axiom audit;
- the allowed axiom policy remains the repository whitelist `propext / Classical.choice / Quot.sound`.

Thus the bounded local factorization/zero-product prerequisite is **written + root-reachable + kernel-built + axiom-audited** at this exact head.  It is still an open PR and is not yet a stable-main consumer anchor.

## Remaining dependency cut

The genuinely missing neutral work is now the regularized factor layer, not local analytic order or finite-product derivative algebra:

1. a finite zero-product quotient that extends analytically across the divided-out zeros (the source `Cf` layer);
2. nonvanishing of that regularized factor on the receiver disc;
3. a local identity splitting `logDeriv f` into the finite zero sum plus `logDeriv regularFactor`;
4. growth transfer for that regular factor sufficient to feed ANT's existing `norm_logDeriv_le_small_disk` theorem.

No claim is made here that those four items are already proved.  The next implementation should stay bounded to this `Cf` layer and reuse the three verified declarations above rather than re-porting the zeta23 global zero hierarchy.
