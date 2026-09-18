# Scalar truncated Perron provenance

This compatibility slice is a source-level reuse of the **project-neutral scalar Perron core** from:

- repository: `subfish-zhou/liu-wang-ternary-goldbach-lean`
- source commit: `b57b7307810c37267e47110d8b5f920e3e681c81`
- source subtree: `BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Perron/`
- auxiliary source: `BombieriVinogradov/Helpers/ComplexAnalysis/ArctanLtSelf.lean`
- source license: Apache-2.0

## Why source-level reuse instead of a Lake dependency

The source repository pins the same Mathlib revision as ANT,
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, so the mathematical API is a
same-revision reuse candidate.  However, the whole source package also exports
library roots named `AnalyticNumberTheory` and `PrimeNumberTheoremAnd`, which
collide with ANT's own roots, and it uses a different `LeanArchitect` revision.
Accordingly ANT does **not** depend on the whole package.

Instead, this PR vendors only the dependency-closed scalar Perron subtree under
its original `BombieriVinogradov` module paths.  The copied source files are
kept unchanged; ANT adds only a sibling `BombieriVinogradov` Lean library and a
four-declaration neutral facade at
`AnalyticNumberTheory.Analysis.TruncatedPerron`.

## Reuse boundary

The integrated theorem is the all-cases scalar estimate
`norm_truncatedPerronKernel_sub_stepWeight_lt` for the normalized finite
vertical integral of `y^s / s`.  It includes:

- the step weight `0 / 1/2 / 1` below / at / above `y = 1`;
- the exact endpoint branch `c / (pi*T)`;
- the off-endpoint error `y^c * min 1 (1/(pi*T*|log y|))`;
- the required rectangle, residue, horizontal-edge, vertical-decay, circular
  arc, and endpoint calculations.

No Dirichlet character, GRH, zero-counting, von Mangoldt coefficient,
application-specific constant, or Mangerel specialization is imported into the
facade.

The immediate named consumer is `UyNewNas/liouville-reflection-lean` PR #20,
whose next sharp-Perron assembly currently needs this scalar kernel before the
source `Series -> Dyadic -> Characters -> Centered` layers can be assessed.

## External duplicate audit

Before extraction, the following were refreshed:

- pinned Mathlib: no indexed `truncatedPerronKernel` implementation;
- `anthropics/formal-math` / zeta23: stronger smoothed explicit-formula and
  contour infrastructure exists, but on a different Mathlib revision and not
  as this sharp all-cases scalar finite-height theorem;
- `subfish-zhou/goldbach-lean`: no competing same-shaped scalar API found;
- exact-same-pin Liu-Wang source above: contains the theorem and its complete
  neutral dependency closure, therefore it is reused rather than re-proved.

Any later extraction of `Series`, `Dyadic`, `Characters`, or `Centered` must
repeat the external-first audit and must not silently widen this compatibility
slice.
