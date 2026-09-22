# Reciprocal vertical-integral provenance audit

Date: 2026-09-22

Consumer: `UyNewNas/liouville-reflection-lean`, half-integer Perron left vertical edge at `Re(s)=1/4`.

## External-first search

Pinned Mathlib is `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.  A repository search of the pinned API surface used by ANT did not reveal a packaged theorem evaluating the symmetric integral

`∫_{-T}^T 1/(|t|+1) dt`

or the exact logarithmically weighted endpoint-freezing inequality needed by the consumer.  Current ANT `main@230ed717546fe38e1141bceaef3ce51f86795152` likewise had no same-object theorem.

Exact-same-pin prior art:

- repository: `subfish-zhou/liu-wang-ternary-goldbach-lean`;
- commit: `b57b7307810c37267e47110d8b5f920e3e681c81`;
- `BombieriVinogradov/Helpers/RealAnalysis/OneDivAbsIntegral.lean::intervalIntegral_one_div_abs_add_one`;
- `BombieriVinogradov/Helpers/RealAnalysis/LogOverOnePlusAbsContinuity.lean::{continuous_log_weight_div_abs_add_one, intervalIntegrable_log_weight_div_abs_add_one}`;
- `BombieriVinogradov/Helpers/RealAnalysis/LogOverOnePlusAbsIntegral.lean::intervalIntegral_log_weight_div_abs_add_one_le`.

These modules use the exact same Mathlib revision as ANT.  Their statements are pure real analysis and do not depend on the source repository's Dirichlet-character, zero-count, selected-height, or contour hierarchy.  Different-revision zeta23 contour work was also checked as prior art; no stronger same-object packaged theorem was identified for this exact reciprocal real integral.

## Minimal adaptation

`AnalyticNumberTheory/Analysis/ReciprocalVerticalIntegral.lean` adapts only the dependency-closed neutral slice:

- `intervalIntegralOneDivAbsAddOne`;
- `continuousLogWeightDivAbsAddOne`;
- `intervalIntegrableLogWeightDivAbsAddOne`;
- `intervalIntegralLogWeightDivAbsAddOneLe`.

The final inequality is intentionally source-faithful: for `C,T ≥ 0`,

`∫_{-T}^T (A + C log(|t|+2)) * (6/(|t|+1)) dt`

is bounded by

`12 * (A + C log(T+2)) * log(T+1)`.

No Perron kernel, L-function, GRH premise, zero selector, or Liouville-specific object is present in ANT.  The LR consumer remains responsible for matching its pointwise quarter-line integrand majorant to this neutral real-analysis theorem.

## Verification gate

The public root imports the module.  `AuditReciprocalVerticalIntegral.lean` fixes a four-declaration trust surface, and the dedicated workflow requires full `PrimeNumberTheoremAnd AnalyticNumberTheory` build, no executable `sorry`/`admit` in the slice, and the repository whitelist `propext / Classical.choice / Quot.sound`.

Until exact-head CI succeeds, this branch is only written and submitted for verification; LR must not repin to it.
