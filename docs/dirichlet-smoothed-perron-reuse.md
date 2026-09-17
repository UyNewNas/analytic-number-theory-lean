# Dirichlet smoothed Perron reuse audit

This note records the source and verification boundary for
`AnalyticNumberTheory.Dirichlet.twistedSmoothedPerron`.

## External source

Canonical source audited before implementation:

- repository: `subfish-zhou/goldbach-lean`
- commit: `09b97db5764ade1246bfb77206baa1b124760958`
- module: `MathlibNt/AnalyticNumberTheory/DirichletL/DirichletLTwistedSmoothedPerron.lean`
- theorem: `DirichletCharacter.twistedSmoothedPerron`
- mathlib revision: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, identical to this ANT branch and its Liouville consumer.

Pinned mathlib and the checked `zeta-23-lean` mirror did not expose an equivalent packaged twisted-smoothed Perron theorem.  The external Goldbach implementation was therefore reused rather than independently rederived.

## ANT adaptation

ANT module: `AnalyticNumberTheory/Dirichlet/TwistedSmoothedPerron.lean`.

The only deliberate adaptation is to reuse ANT's already verified
`twistedVonMangoldtLSeries_eq_negLogDerivLFunction` seam instead of copying Goldbach's thin
`DirichletLFoundation` wrapper.  The theorem remains neutral: it assumes neither GRH nor
nonprincipality and contains no contour shift, Goldbach object, Liouville defect, or
application parameter choice.

## Audit

The theorem is root-exported, listed in `AuditDirichlet.lean`, and covered by the focused exact-count audit. `AuditPerron.lean` additionally places it under the repository public-theorem axiom whitelist without duplicating the large legacy `Audit.lean` source. The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The next reusable seam must be audited against the same Goldbach commit before work starts: right-vertical integrability, quantitative right tails, and horizontal-contour bounds already exist externally and must not be independently reinvented.
