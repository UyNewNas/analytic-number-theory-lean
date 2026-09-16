# Analytic Number Theory in Lean

Reusable formalized analytic-number-theory infrastructure for downstream projects.

The public entry point is `AnalyticNumberTheory.lean`. Current reusable layers include prime-distribution and Mertens APIs, sieve and large-sieve infrastructure, and a neutral Dirichlet-character layer with concrete Dirichlet-`L` GRH predicates, zero-free rectangles, character orthogonality, principal/nonprincipal decomposition, and finite character second moments.

Application-specific objects and hypotheses should remain in downstream repositories. In particular, this repository should host reusable mathematical interfaces and proofs rather than Liouville-reflection, Goldbach, or paper-specific endgame statements.

See `ROADMAP.md` for the demand-driven maintenance policy and `UPSTREAM.md` for provenance notes.
