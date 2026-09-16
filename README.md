# analytic-number-theory-lean

A standalone Lean 4 library for the analytic-number-theory infrastructure used by the Chen theorem formalization.

The repository is intentionally application-neutral: it packages prime-counting estimates, Mertens-type results, sieve identities, large-sieve estimates, and related reusable lemmas without importing the downstream Chen development.

## Current status

- The public `AnalyticNumberTheory` API builds without `sorry`/`admit`.
- CI scans executable Lean source for placeholders before building.
- CI audits the public theorem surface against the allowed axiom set `propext`, `Classical.choice`, and `Quot.sound`.
- Downstream applications should depend on stable public modules rather than reaching into compatibility implementation files.

## Main public areas

- `AnalyticNumberTheory/PrimeDistribution`
- `AnalyticNumberTheory/Mertens`
- `AnalyticNumberTheory/Sieve`
- `AnalyticNumberTheory/LargeSieve`

See `ROADMAP.md` and `UPSTREAM.md` for maintenance and provenance notes.
