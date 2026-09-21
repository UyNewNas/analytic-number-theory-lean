# Dirichlet L-function conjugation provenance audit

Date: 2026-09-21

Consumer: `UyNewNas/liouville-reflection-lean`, selected-height left-strip reflection seam.  The
consumer needs to transfer the same selected ordinate / zero-separation information between a
character and its inverse without introducing a second selected height.

## External-first search

Current ANT base is `main@38c82b04e243991719d5be363311a3b66d71cba8`, pinned to Mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

Exact-same-pin source:

- repository: `subfish-zhou/liu-wang-ternary-goldbach-lean`;
- commit: `b57b7307810c37267e47110d8b5f920e3e681c81`;
- source modules:
  - `BombieriVinogradov/Helpers/DirichletCharacter/ComplexConjugation.lean`;
  - `BombieriVinogradov/Proof/SiegelWalfisz/ZeroFree/LFunctionConjugation.lean`;
- key declaration:
  `BombieriVinogradov.SiegelWalfisz.DirichletCharacter.LFunction_inv_eq_conj_conj`, proving
  `chi⁻¹.LFunction s = conj (chi.LFunction (conj s))` for nonprincipal complex Dirichlet
  characters.

The same source first proves coefficient conjugation via `MulChar.star_apply'`, then conjugation of
the naive `LSeries`, and finally extends the equality to the entire nonprincipal L-function by
analytic uniqueness.  This dependency closure is small and independent of Siegel--Walfisz,
zero-count, selected-height, completed-zero, contour, or GRH arguments.

Different-revision prior art:

- `anthropics/formal-math@fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`;
- `zeta23/Zeta23/ThmE/SeamL.lean::LFunction_conj` proves the equivalent Schwarz-reflection
  statement and then transports analytic order/multiplicity.  Its Mathlib revision differs, so it
  is source/API prior art rather than a dependency.

Current ANT main was searched for `conj_apply_eq_inv_apply`,
`conj_LSeries_conj_eq_inv_LSeries`, and `LFunction_inv_eq_conj_conj`; no packaged equivalent was
present.  ANT already contains the neutral helper
`AnalyticNumberTheory.Dirichlet.inv_ne_one_of_ne_one` in `CompletedReflection.lean`, so the source's
separate primitive-inverse helper file is not duplicated.

## Minimal extraction

`AnalyticNumberTheory/Dirichlet/LFunctionConjugation.lean` keeps exactly four neutral statements:

1. `conj_apply_eq_inv_apply`;
2. `conj_natCast_cpow_conj`;
3. `conj_LSeries_conj_eq_inv_LSeries`;
4. `LFunction_inv_eq_conj_conj`.

The adaptation keeps the source proof structure and attribution while reusing ANT's existing
`inv_ne_one_of_ne_one`.  It intentionally omits the source's parity helpers because they are not
needed for the conjugation theorem, and it does not copy the much larger selected-height whole-strip
bound.

This is a project-neutral seam: no Liouville object, selected-height parameter, GRH predicate,
zero-count, contour, or Mangerel-specific constant appears in the public API.

## Verification plan

The branch is root-imported through `AnalyticNumberTheory.lean` and has a dedicated
`AuditDirichletLFunctionConjugation.lean` axiom audit.  Merge requires exact-head GitHub CI to show:

- executable `sorry`/`admit` rejection for the new source/audit files;
- build of `AnalyticNumberTheory.Dirichlet.LFunctionConjugation` and the root module;
- exactly four axiom reports with no axioms beyond the repository whitelist
  `propext`, `Classical.choice`, `Quot.sound`;
- the repository-wide build/trust workflow green on the same SHA.

Until those checks succeed, the branch is only a staged adaptation and must not be used as a stable
downstream pin.
