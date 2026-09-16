# analytic-number-theory-lean

Reusable analytic number theory infrastructure in Lean 4.

This repository is maintained as a demand-driven foundation for downstream formalizations.  It
contains reusable prime-distribution, sieve, large-sieve, Mertens, and Dirichlet-character
infrastructure rather than application-specific theorem statements.

## Stable public entry point

Downstream projects should import `AnalyticNumberTheory` or the specific child module they need.
The historical `PrimeNumberTheoremAnd` tree is retained as a compatibility implementation layer;
new reusable APIs live under `AnalyticNumberTheory/`.

## Dirichlet core

The reusable Dirichlet layer currently includes:

- concrete GRH predicates for mathlib's analytically continued Dirichlet `LFunction`;
- generic zero-free rectangles and the GRH implication;
- two- and three-factor character orthogonality at prime moduli;
- principal/nonprincipal finite-sum decomposition;
- finite unweighted character second moments;
- exact weighted finite character second moments
  `weightedCharacterSumOn_secondMoment_prime`.

The weighted moment theorem is intentionally coefficient-agnostic: applications such as Liouville
or Möbius character sums supply their own weights downstream.  This keeps application-specific
defect, phase, or Goldbach statements out of the foundation layer.

## Trust boundary

Tracked Lean sources are built in CI with executable `sorry` / `admit` rejection.  Public theorem
axioms are audited against the repository whitelist:

- `propext`
- `Classical.choice`
- `Quot.sound`

Focused reusable slices may add dedicated audits, but they do not weaken the repository-wide build
or axiom checks.

## Development policy

New work should have a named downstream consumer or fill a clearly reusable mathematical gap.
Prefer neutral interfaces with explicit hypotheses and constants.  Do not import application
projects back into ANT merely to prove an application theorem; instead expose the general lemma
here and specialize it downstream.

See `ROADMAP.md`, `UPSTREAM.md`, and the open issues/PRs for current maintenance work and provenance.
