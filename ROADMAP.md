# Maintenance and reuse roadmap

Updated 2026-09-14. The library retains its prime-distribution, Mertens, and
reusable sieve foundations. Work is selected by a concrete theorem consumer,
not by the size of the historical Chen/Pan backlog.

## Completed downstream and retained upstream

[subfish-zhou/goldbach-lean](https://github.com/subfish-zhou/goldbach-lean) credits
this library and `UyNewNas/chen-theorem-lean` as upstream foundations and provides
completed Chen and Li–Liu applications. Reference snapshot:
`df1f3b3b721c9a0b5e38ba39d5c0e3c2a1d72f59` (2026-09-08).

- [Provenance](https://github.com/subfish-zhou/goldbach-lean/blob/df1f3b3b721c9a0b5e38ba39d5c0e3c2a1d72f59/docs/PROVENANCE.md)
- [Theorem interfaces](https://github.com/subfish-zhou/goldbach-lean/blob/df1f3b3b721c9a0b5e38ba39d5c0e3c2a1d72f59/docs/THEOREMS.md)
- [Source architecture](https://github.com/subfish-zhou/goldbach-lean/blob/df1f3b3b721c9a0b5e38ba39d5c0e3c2a1d72f59/docs/ARCHITECTURE.md)

The downstream package includes an adapted local source closure. Reuse back into
ANT therefore needs a source/dependency comparison, not merely a Lake version bump.

## Work classification

| Class | Treatment |
| --- | --- |
| Application completed downstream | Link the completed application instead of independently reconstructing it here. |
| Old formulation or route superseded | Preserve its mathematical findings, remove it from the active proof queue, and record why; do not call the old proposition proved. |
| Reusable result retained on demand | Keep the precise API and activate only the portion needed by a named consumer. |

[Issue #1](https://github.com/UyNewNas/analytic-number-theory-lean/issues/1) is the
work register. Existing CI repairs remain limited maintenance, not a reason to
restart every open branch. General Pan/BV statements require exact comparison
of weights, source support, maxima, main terms, and uniform quantifiers with
proved downstream instances.

## First bounded work item: genuine Li API (#69 / existing PR #70)

This is the first source comparison, not a second implementation project.
PR #70 currently changes only `PrimeDistribution/PrimeNumberTheorem.lean`; retain
its public endpoint convention and reuse its branch when implementation resumes.

### Exact source correspondence

Existing [PR #70](https://github.com/UyNewNas/analytic-number-theory-lean/pull/70),
head `88f20482d3c1ae96e2034e6da0f3ae36c215e969`, defines

```text
primeLogIntegral(x) = integral from 2 to x of 1/log(t)
```

The inspected downstream
[`Arithmetic/LiuLogarithmicIntegral.lean`](https://github.com/subfish-zhou/goldbach-lean/blob/df1f3b3b721c9a0b5e38ba39d5c0e3c2a1d72f59/MathlibNt/SieveTheory/Arithmetic/LiuLogarithmicIntegral.lean)
defines

```text
liuLogarithmicIntegral(kappa, x) = kappa + integral from 2 to x of 1/log(t).
```

Thus the definitions agree at `kappa = 0`; the downstream normalization
`kappa = 2/log(2)` is an additive shift, not a competing Li convention. This
source-level identity has not yet been compiled as a cross-project bridge.

| Existing ANT PR #70 | Downstream source | Bounded next action |
| --- | --- | --- |
| `primeLogIntegral` / `primeLogIntegral_def` | `liuLogarithmicIntegral` / `liuLogarithmicIntegral_sub_normalization` | Preserve the zero-at-two public convention; expose additive normalization only where consumed. |
| `primeLogIntegral_eq_main_add_tail`, currently `4 ≤ x` with a set integral over `Icc` | `liuLogarithmicIntegralRemainder_eq`, `2 ≤ x` with an interval integral | Reuse the integration-by-parts argument to obtain the full `2 ≤ x` range and reconcile interval/set-integral notation. |
| No corresponding neutral lemma in the inspected PR patch | Integrability and nonnegativity lemmas above `2`; `div_log_le_liuLogarithmicIntegral` | Extract only the lemmas needed by the main-term consumer, retaining provenance. |
| `primeCounting_partialSummation` | Distribution/PNT layers beyond the Li definition module | Keep quantitative `pi - Li` estimates as a separate checked target; the elementary Li module alone does not supply them. |

The downstream file directly imports `Liu.Weights.LiuWeightPaperQ` as well as
Mathlib analysis. The inspected elementary definitions/proofs above contain no
explicit Chen-weight references; a neutral extraction must still verify its
complete import requirements rather than carry that application dependency
into ANT. Do not add a dependency from ANT back to the Goldbach application.

### Acceptance for this bounded slice

- Preserve the existing `primeLogIntegral` meaning and PNT exports.
- Check the normalization and endpoint bridges with the pinned Lean/mathlib.
- Record the downstream commit and preserve attribution for adapted proofs.
- Keep the existing full-build/source-scan/axiom checks; identify baseline CI
  problems separately from the proposed API changes.
- Demonstrate use by the distribution-main-term interface in #69. Proceed to a
  quantitative `pi - Li` or weighted-BV implementation only for the exact needed
  statement; do not assume an application-specific theorem proves general Pan.

No Li backport or new analytic theorem is included in this roadmap change.

## Existing results and historical detail

PNT, Mertens II, the exact Mertens product, and the constant-identification chain
remain available; the source and audits are unchanged. Keep the existing
`PrimeNumberTheoremAnd` provenance boundary.

The [previous roadmap](https://github.com/UyNewNas/analytic-number-theory-lean/blob/5536c2d8c387d4bb5438478636c25d7b093206d2/ROADMAP.md)
preserves the earlier release milestones. `PAN_PROOF_ATLAS.md` remains a
historical dependency record; its unchecked items are not all active tasks.
