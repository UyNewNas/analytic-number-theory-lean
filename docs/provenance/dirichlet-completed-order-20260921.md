# Dirichlet completed-L zero multiplicity provenance audit

Date: 2026-09-21

Consumer: `UyNewNas/liouville-reflection-lean`, selected-height / Jensen zero bookkeeping on the positive critical strip. The immediate downstream need is to compare ordinary Dirichlet-L zero multiplicity with the symmetric completed-L multiplicity used by the same-pin selected-height source, without importing that source's global zero-index/count hierarchy.

## External-first search

Pinned Mathlib is `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. ANT already exposes the symmetric completion and positive-half-plane gamma regularity at this same pin through:

- `AnalyticNumberTheory/Dirichlet/CompletedReflection.lean`;
- `AnalyticNumberTheory/Dirichlet/GammaFactorRegularity.lean`.

Exact-same-pin source:

- repository: `subfish-zhou/liu-wang-ternary-goldbach-lean`;
- commit: `b57b7307810c37267e47110d8b5f920e3e681c81`;
- declaration: `BombieriVinogradov/Proof/SiegelWalfisz/ZeroFree/CompletedLFunctionOrder.lean::analyticOrderNatAt_symmetricCompletedLFunction_eq_LFunction`;
- statement: for a nonprincipal complex Dirichlet character and `0 < Re(s)`, the analytic zero multiplicity of the symmetric completed L-function equals that of the ordinary L-function.

The same source also has `LiuWang/Proof/DirichletZeroCount/Argument/CompletedCount.lean::completed_zero_iff_ordinary`, while its selected-height machinery indexes zeros by `BombieriVinogradov/.../CompletedZeroIndex.lean::SymmetricCompletedZeroIndex`, an alias of the custom `Complex.Hadamard.divisorZeroIndex₀`. That index in turn depends on `PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/DivisorIndex.lean` and a substantially larger divisor/canonical-product support tree.

The current ANT main does not contain that custom divisor-index module. Importing it merely to connect one downstream finite Jensen representation to source selected-height terms would therefore be a non-minimal dependency expansion.

Different-revision prior art remains `anthropics/formal-math@fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` (zeta23), whose local-count machinery likewise transports multiplicities through affine zero representations. It is useful as a proof-pattern reference but is not a drop-in dependency at ANT's pinned revision.

## Minimal extraction decision

This slice extracts exactly one neutral theorem into `AnalyticNumberTheory/Dirichlet/CompletedOrder.lean`:

`AnalyticNumberTheory.Dirichlet.analyticOrderNatAt_symmetricCompletedLFunction_eq_LFunction`.

The proof reuses ANT's existing symmetric completion and gamma regularity. On the open positive half-plane it writes the symmetric completion locally as

`N^(s/2) * (L(s,chi) * gammaFactor(s,chi))`,

proves the normalization and gamma factor analytic and nonzero, and removes their zero orders by the analytic-order product law. No GRH, zero-free region, selected height, zero index, contour, Perron term, or Liouville object appears in the theorem.

Decision: **GO** for this one multiplicity seam; **NO-GO** for importing `SymmetricCompletedZeroIndex`, `DivisorIndex`, completed-zero window counting, or the full Liu-Wang selected-height hierarchy into ANT at this stage. LR should first consume the neutral multiplicity equality in its finite actual-zero/Jensen model and only extract a further neutral bridge if a concrete representation mismatch remains.

## Verification policy

The new declaration is root-reachable through `AnalyticNumberTheory.lean` and receives a dedicated `AuditDirichletCompletedOrder.lean` axiom report plus `Dirichlet completed-order audit` workflow. The workflow runs the module and root build, rejects executable `sorry`/`admit`, and enforces the existing axiom whitelist `propext`, `Classical.choice`, `Quot.sound`.

No branch is a downstream anchor until the exact PR head has completed those checks successfully and any integration merge has passed the repository's required checks.
