# Fixed-height rectangle orientation reuse

Date: 2026-09-18

## Named consumer

The immediate consumer is `UyNewNas/liouville-reflection-lean`, branch
`formalize/core-and-energy-completion`.

At commit `0076bfc4524c0450073bdaf024884f1dc43393f0` the downstream project had to
re-prove, in project-local names, the purely algebraic fixed-height identity
that rewrites the right vertical Perron integral as a rectangle integral plus
the bottom/left/top broken boundary.  Its current root-reachable bridge is
`LiouvilleReflection/MangerelFixedHeightContourAlgebra.lean`; later commit
`22fd6e755a42bb8834c46652aaa36cec70fa2497` records the reuse seam explicitly.

That is enough demand to justify extracting the existing project-neutral source
identity into stable ANT.  Mangerel endpoint constants, dyadic subtraction,
Dirichlet-character specialization, residue sums, GRH and Liouville statements
remain downstream.

## Exact-same-pin source selected

Source repository:
`subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`.

ANT and this source both pin Mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

Exact source files:

- `BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Contour/Definitions.lean`
  — blob `42211455ea9487c7b7a2884fbd48cf131968bf2a` at the selected source revision;
- `BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Contour/Rectangle.lean`
  — blob `5b89e7f9978c7b616b0cfcdb667b872d59c39eac`.

The dependency closure is bounded: the definitions file imports only
`PrimeNumberTheoremAnd.ResidueCalcOnRectangles`, which ANT already carries and
builds.  The rectangle file imports only the definitions file.  No centered
regularization, zero-count, Perron endpoint machinery, or Dirichlet-L hierarchy
is pulled in.

The reused declarations are:

- `BombieriVinogradov.SiegelWalfisz.explicitFormulaContourLowerLeft`;
- `BombieriVinogradov.SiegelWalfisz.explicitFormulaContourUpperRight`;
- `BombieriVinogradov.SiegelWalfisz.explicitFormulaBrokenBoundaryIntegral`;
- `BombieriVinogradov.SiegelWalfisz.VIntegral'_eq_rectangle_add_brokenBoundary`.

The stable ANT import boundary is
`AnalyticNumberTheory.ComplexAnalysis.RectangleBoundary`; the original namespace
and proof text are preserved rather than wrapped in a second theorem family.

## Other prior art checked

Canonical zeta23/formal-math was rechecked at
`anthropics/formal-math@fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`.
`zeta23/Zeta23/Analytic/RectangleLogDeriv.lean` contains the stronger generic
weighted argument-principle family including
`rectangleIntegral'_mul_logDeriv_of_poles`,
`rectangleIntegral'_mul_logDeriv`, and
`rectangleIntegral'_mul_logDeriv'`; `Zeta23/ThmE/ContourChi.lean` specializes
that machinery to Dirichlet characters.  It uses a different Mathlib revision
and a substantially larger semantic/dependency surface.  It is prior art for
the later residue/argument-principle step, not a better replacement for this
one-line orientation seam.

Current ANT `main@e0d91ef2a1b6cf30341cbb5313313d39cf928c2c` was searched for
`VIntegral'_eq_rectangle_add_brokenBoundary`; no existing copy was present.
Canonical same-revision Goldbach remains an important source for other contour
and smoothed-Perron components, but no competing packaged fixed-height
orientation seam was found in the current ANT surface.

## Integration decision

Reuse the exact-same-pin Liu--Wang two-file slice and audit it directly.  Do not
port zeta23's weighted argument principle yet; do not revive the long-lived ANT
#76 branch; do not import the Liu--Wang centered/regularized contour hierarchy.
A later generic residue theorem is justified only if the downstream dyadic
fixed-height proof exposes a named, project-neutral consumer with a bounded
closure.
