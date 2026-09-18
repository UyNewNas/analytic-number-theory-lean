# Dyadic explicit-formula origin cancellation provenance

## Consumer and scope

The named consumer is `UyNewNas/liouville-reflection-lean` PR #20.  Its fixed-height
Mangerel contour uses the sharp dyadic interval `(P,2P]`, hence the actual analytic
object is the endpoint difference rather than either unregularized endpoint in
isolation.

The reusable statement is

```text
F_{2P}(s) - F_P(s)
 = - (L'/L)(s) * P^s * ((2^s - 1) / s).
```

The rightmost quotient is removable at `s = 0`.  This module stops at the
project-neutral algebra/meromorphic-order seam; it does not assert a contour
residue theorem, boundary zero-freeness, zero count, GRH estimate, or any
Liouville/Mangerel conclusion.

## External-first audit — 2026-09-19

Pinned Mathlib revision:
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

Same-pin Liu--Wang source inspected at
`subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`:

- `.../Residue/Origin/KernelDifference.lean` packages
  `originCpowDifferenceQuotient`, its meromorphicity, punctured limit at zero,
  and nonnegative meromorphic order at zero;
- `.../Residue/Origin/RegularizedDefinitions.lean` defines the single-endpoint
  double-pole correction; crucially that correction is independent of the
  endpoint `x`, so it cancels exactly in a dyadic endpoint difference;
- `.../Residue/Origin/ScaledRegularizedIdentity.lean` uses the same removable
  quotient in the origin regularization algebra;
- `.../Residue/Poles/LogDerivativeSimple.lean` and
  `.../Residue/Origin/RegularizedSimpleOn.lean` handle the later simple-pole
  layer, which is intentionally not migrated in this PR.

Current ANT `main@79ce488028ab2af17908aee0ee25eb41e6eb1f1e` already contains the
verified source-adapted neutral quotient from PR #102 and the existing
`Dirichlet.explicitFormulaIntegrand`; it does not yet package their dyadic
factorization.  Searches in `anthropics/formal-math` / zeta23 and canonical
`subfish-zhou/goldbach-lean` found related explicit-formula/zero machinery but
no same-pinned packaged theorem with this exact endpoint-difference origin
factorization.

`AxiomMath/PrimeNumberTheoremAnd@75c7dffd3ddfe2bda7c33264c780a97486f8303d`
was also checked for the generic pole-order pattern.  Its
`IEANTN/KadiriEq12Helpers.lean::hasSimplePolesOn_eq12_integrand` confirms the
standard order bookkeeping `log-derivative order >= -1` plus analytic-cofactor
order `>= 0`; that is later prior art for the simple-pole assembly, not a reason
to duplicate its zeta-specific theorem here.

## Reuse decision

Add only:

- `explicitFormulaDyadicIntegrand`;
- `explicitFormulaDyadicOriginKernel`;
- exact endpoint-difference factorization;
- global meromorphicity of the positive-`P` dyadic kernel;
- nonnegative meromorphic order of that kernel at the origin.

The quotient facts are reused from ANT PR #102 rather than copied again.
The downstream Liouville project should become a thin naming/parameter adapter
once this PR is verified and merged.

`AuditExplicitFormulaDyadicOrigin.lean` prints axioms for the three theorem
statements.  The dedicated workflow requires exactly three reports and accepts
only `propext`, `Classical.choice`, and `Quot.sound`.
