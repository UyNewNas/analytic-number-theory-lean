# Origin complex-power difference quotient provenance

## Named consumer

`UyNewNas/liouville-reflection-lean` PR #20 currently needs to treat the dyadic
explicit-formula difference at `s = 0` without pretending that each unregularized
single-endpoint Perron integrand has only simple poles on a rectangle containing
the origin.

The neutral analytic atom is the removable quotient

```text
((x : ℂ)^s - 1) / s.
```

It belongs in ANT because it contains no Dirichlet character, GRH, zero count,
Liouville defect, Mangerel parameter, or project-specific contour geometry.

## External-first audit — 2026-09-19

Pinned ANT Mathlib revision remains
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

Exact same-pin source inspected:

- repository: `subfish-zhou/liu-wang-ternary-goldbach-lean`;
- commit: `b57b7307810c37267e47110d8b5f920e3e681c81`;
- module:
  `BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Residue/Origin/KernelDifference.lean`;
- source blob: `50471e9ffecd7a83e393bf5409da5302113f3d23`;
- declarations:
  `originCpowDifferenceQuotient`,
  `meromorphic_originCpowDifferenceQuotient`,
  `tendsto_originCpowDifferenceQuotient_zero`,
  `meromorphicOrderAt_originCpowDifferenceQuotient_zero_nonneg`.

The proof uses only pinned Mathlib's complex `cpow` derivative, `slope`, and
meromorphic-order API.  The source theorem is therefore directly source-adaptable
without importing the Liu--Wang package or any of its Dirichlet/explicit-formula
dependency tree.

Related source modules were also inspected before choosing this bounded seam:
`ScaledRegularizedIdentity.lean`, `RegularizedSimpleOn.lean`, and
`Residue/Main.lean`.  Those modules solve the larger single-endpoint origin
regularization problem.  They are deliberately not imported or migrated here.
The immediate downstream dyadic consumer can exploit the smaller cancellation
`(2^s - 1) / s`, so widening ANT to the complete regularized residue hierarchy
would be unjustified at this stage.

Search of current ANT `main@ecd3530d964ee2837ce34dede97237b5606561ce`
found no existing `regularizedExplicitFormulaIntegrand` or packaged origin-cpow
difference quotient.  Current ANT already contains the generic log-derivative
residue and unregularized Dirichlet explicit-formula atoms; this addition is
non-overlapping.

## Adaptation decision

Source-adapt the four neutral declarations into
`AnalyticNumberTheory.ComplexAnalysis.OriginCpowDifference`, retaining the same
mathematics and proof shape under the ANT namespace.  Do not copy Liu--Wang's
regularized Dirichlet integrand, pole-set hierarchy, boundary theorem, or full
rectangle residue assembly.

`AuditOriginCpowDifference.lean` is the focused trust probe.  The dedicated
workflow requires exactly three theorem axiom reports and accepts only
`propext`, `Classical.choice`, and `Quot.sound`; the definition itself introduces
no proof dependency.
