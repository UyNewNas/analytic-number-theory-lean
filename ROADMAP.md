# Maintenance and reuse roadmap

Direction adopted 2026-09-14; refreshed 2026-09-17 after the main/dev integration sprint.

ANT is maintained as a reusable analytic-number-theory foundation. Work is activated by a concrete theorem consumer and an exact missing interface, not by the size of the historical Chen/Pan backlog.

## Repository roles

- `UyNewNas/analytic-number-theory-lean`: reusable neutral infrastructure.
- `UyNewNas/chen-theorem-lean`: upstream foundation/provenance/history; the independent Chen-completion effort remains retired.
- `subfish-zhou/goldbach-lean`: completed downstream Chen/Li–Liu application and an important source of reusable formalized analytic lemmas.
- `UyNewNas/liouville-reflection-lean`: current named consumer driving selected reusable Dirichlet/GRH extraction through ANT PR #76.

Issue #1 is the authoritative rolling work register. PR descriptions carry exact per-branch verification anchors.

## Completed integration sprint

The long-separated `dev` and historical `main` work was reconciled through bounded slices rather than a branch-precedence merge:

1. #73 repaired the Bombieri–Davenport baseline.
2. #75 de-duplicated V1/V3 LCM-weight proofs while preserving all public compatibility names.
3. #70 integrated the genuine logarithmic-integral API, including the full `x ≥ 2` integration-by-parts bridge and the neutral
   `Nat.primeCounting ⌊x⌋₊ - (2 / log 2 + primeLogIntegral x) = O(x / log^2 x)` consequence.
4. #79 restored main-only Pan/assembly modules onto the repaired dev baseline.
5. #80 restored the later `PanVaughanPointwise` / `PanChebyshevMainStep` layer.
6. #81 restored the isolated Bombieri–Davenport type-II / `vaughanThird` bridge.
7. #82 reconciled the public axiom-report parser without weakening the whitelist or replacing the fixed-count gate.
8. #83 built the combined main tree, restored main's complete public audit registry, measured the combined registry, and locked the public expected count at **463**.

PR #83 exact head `32e538c6c3ce386f25751b874a24da905a5b5540` passed ordinary workflow `35200941907` (#470) and focused reconciliation workflow `35200941881` (#30). The default branch's active linear-history rule prevented a merge commit and GitHub could not rebase the merge-shaped integration branch, so the verified tree was integrated through the PR as squash commit `ba74a8771eb34c21fccf9c6230dca71ff943bb2b`. The squash commit's tree SHA is exactly the same as the verified PR head tree.

The integrated trust boundary is:

- executable `sorry` / `admit` rejection;
- full `PrimeNumberTheoremAnd AnalyticNumberTheory` build;
- 10-report genuine-Li focused audit;
- fixed **463-report** public axiom audit;
- allowed axioms only `propext`, `Classical.choice`, `Quot.sound`.

A post-integration push run on `main` is still the final branch-level verification record for the squash commit; do not substitute the pre-merge PR run for that verdict.

## External-first rule

Before implementing a nontrivial new API, first inspect current pinned Mathlib and relevant existing Lean formalizations. For current Dirichlet-L / Perron / explicit-formula work, mandatory references include:

- `subfish-zhou/goldbach-lean`, pinned provenance snapshots recorded in the consuming PR;
- canonical `anthropics/formal-math`, project `zeta23/`;
- any other discoverable Lean repository or PR with a matching theorem surface.

Record the external revision, exact declaration/module, hypotheses and quantifier order, dependency footprint, and whether the result is directly reusable or requires a neutral adaptation. Different Lean/Mathlib revisions are a compatibility problem, not a reason to re-prove an existing theorem from scratch.

In particular, do not independently recreate already-formalized:

- smoothed twisted Perron inversion and its right-line support;
- effective finite-rectangle Dirichlet `L'/L` estimates;
- conditional natural-order Dirichlet-series infrastructure;
- χ-side zero counts, logarithmic-derivative partial fractions, good-height selection, contour estimates, or explicit-formula machinery.

## Integrated bounded reuse: genuine Li (#70)

ANT keeps the normalization

```text
primeLogIntegral x = ∫ t in 2..x, 1 / log t
primeLogIntegral 2 = 0
```

while the pinned downstream Li–Liu source uses an additive constant

```text
liuLogarithmicIntegral κ x = κ + primeLogIntegral x.
```

That correspondence was machine-checked against the pinned downstream declaration in a one-off verification probe, then the network/downstream probe was removed again. Goldbach remains provenance/test input rather than a permanent ANT dependency.

Do not automatically promote the neutral `O(x/log^2 x)` result to arbitrary logarithmic saving, `WeightedBVAtOne`, supported transport, or a general Pan theorem without a named consumer and an exact source/type match.

## Integrated bounded maintenance: LCM-weight de-duplication (#75)

The neutral shared layer provides

- `LcmWeightBounds.harmonic_Icc_le`;
- `LcmWeightBounds.card_multiples_Icc`;
- `LcmWeightBounds.lcm_inv_sum_le`;
- `LcmWeightBounds.divisorCountSq_sum_le`.

Existing V1 and V3 public theorem names remain wrappers over this layer, and established consumers continue to compile. The refactor removed roughly 900 lines of duplicate proof implementation without adding downstream application dependencies.

## Active consumer-backed reuse lane: PR #76

PR #76 remains a separate reusable-analytic lane driven by `liouville-reflection-lean`. Its accumulated scope includes neutral pieces of:

- Dirichlet characters / GRH facades;
- character orthogonality, decomposition, and moment identities;
- dyadic prime windows and weight-removal interfaces;
- twisted von-Mangoldt windows and partial sums;
- `-L'/L` / right-edge majorants;
- provenance-preserving adaptations of existing finite-rectangle and smoothed-Perron machinery.

Do **not** merge the long historic PR wholesale. The correct integration strategy is to identify stable consumer-backed logical blocks, reconcile each block against current `dev`/`main`, preserve external provenance, and require exact-head build + axiom audit before downstream repinning.

Newer commits on #76 are not considered verified merely because an earlier head was green. Read its actual GitHub head and workflow results each round.

## Work classification

| Class | Treatment |
| --- | --- |
| Application completed downstream | Link the application; do not independently rebuild it here. |
| Neutral theorem already formalized elsewhere | Reuse directly or adapt minimally with provenance and local recompilation. |
| Reusable theorem with a named ANT consumer | Implement/extract the exact missing interface and audit it. |
| Historical or superseded route | Preserve findings and provenance, but remove it from the active queue. |
| Generalization without a concrete consumer | Keep dormant. |

## Current stop / next ordered work

1. Finish verification of the post-#83 `main` push commit.
2. Refresh and integrate this documentation PR only against that stabilized main tree; its old pre-reconciliation CI is not sufficient.
3. Keep #76 broad growth frozen while splitting/reconciling stable consumer-backed blocks.
4. Before any further Perron, zero-count, explicit-formula, effective `L'/L`, weighted-BV, or general-Pan work, perform an external-first API audit and record the exact gap.

Never use `sorry`/`admit`, custom axioms, equal-strength application hypotheses, weakened audit gates, force pushes, or branch deletion to manufacture progress.

## Historical detail

PNT, Mertens II, the exact Mertens product, the constant-identification chain, sieve foundations, and the Pan proof atlas remain part of the repository history. Historical atlas checkboxes are not automatically active tasks. The pre-maintenance roadmap remains available from the old main snapshot `5536c2d8c387d4bb5438478636c25d7b093206d2`.
