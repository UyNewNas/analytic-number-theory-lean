# Maintenance and reuse roadmap

Direction adopted 2026-09-14; status refreshed 2026-09-15. The library retains
its prime-distribution, Mertens, and reusable sieve foundations. Work is selected
by a concrete theorem consumer, not by the size of the historical Chen/Pan backlog.

## Completed downstream and retained upstream

[subfish-zhou/goldbach-lean](https://github.com/subfish-zhou/goldbach-lean) credits
this library and `UyNewNas/chen-theorem-lean` as upstream foundations and provides
completed Chen and Li–Liu applications. Reference snapshot for the first Li reuse
comparison: `df1f3b3b721c9a0b5e38ba39d5c0e3c2a1d72f59` (2026-09-08).

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
restart every open branch. General Pan/BV statements require exact comparison of
weights, source support, maxima, main terms, levels, and quantifier order with
proved downstream instances.

## First bounded reuse slice: genuine Li API (#69 / PR #70)

This source comparison has now produced a bounded neutral ANT implementation; it
is not a second Chen application project. Existing
[PR #70](https://github.com/UyNewNas/analytic-number-theory-lean/pull/70), head
`6d7297966e8c2d3634a4265f6eba4b58d9ce3e30`, preserves the public convention

```text
primeLogIntegral(x) = integral from 2 to x of 1/log(t),
primeLogIntegral(2) = 0.
```

The inspected downstream
[`Arithmetic/LiuLogarithmicIntegral.lean`](https://github.com/subfish-zhou/goldbach-lean/blob/df1f3b3b721c9a0b5e38ba39d5c0e3c2a1d72f59/MathlibNt/SieveTheory/Arithmetic/LiuLogarithmicIntegral.lean)
uses

```text
liuLogarithmicIntegral(kappa, x) = kappa + integral from 2 to x of 1/log(t).
```

Thus `liuLogarithmicIntegral kappa x = kappa + primeLogIntegral x` at the source
normalization level. ANT keeps the zero-at-two convention and does not depend on
the downstream Goldbach/Liu application layer.

PR #70 now contains the neutral slice required by #69:

- definition/unfolding, zero-at-two, additive normalization, and nonnegativity;
- exact prime-counting partial summation;
- `primeLogIntegral_eq_main_add_tail` on the full source range `2 ≤ x`, including
  the interval/set-integral reconciliation needed by the adapted proof;
- exact `primeCounting_sub_normalizedLi_eq`;
- endpoint and integral remainder bounds;
- the quantitative consequence

```text
Nat.primeCounting ⌊x⌋₊ - (2 / log 2 + primeLogIntegral x)
  = O(x / log^2 x).
```

The adapted proof ideas retain the downstream source revision and attribution.
No `LiuWeightPaperQ` or other Goldbach application dependency is imported into ANT.

### Verification boundary

At PR #70 head `6d7297966e8c2d3634a4265f6eba4b58d9ce3e30`, workflow run
`34824232102` reports the executable `sorry`/`admit` scan and the additive
`Audit genuine Li slice` gate as **success**. The repository-wide build still
fails later in the pre-existing `LargeSieve/BombieriDavenport.lean` dev baseline.
The focused gate is additive; it does not replace or weaken the normal full build
and trust audit.

The baseline repair remains separate in
[PR #73](https://github.com/UyNewNas/analytic-number-theory-lean/pull/73): it is an
exact restoration of the previously verified Bombieri–Davenport file, has a
successful repository-wide build/trust audit on head
`28df7a866bf4c1cafd791ffdf2a64cb9e3cafae5`, and is ready for review but unmerged.
After an explicit #73 integration, re-run/rebase #70 against the resulting `dev`
and require the normal repository-wide checks before integration.

### Dormant stronger interfaces

Do not continue automatically from the neutral `O(x/log^2 x)` result to arbitrary
fixed logarithmic saving, `WeightedBVAtOne`, supported transport, or a general Pan
theorem. Activate one only when a named consumer requires the exact statement and
the source/type comparison matches its weights, support, main term, level, maxima,
and quantifier order.

## Next small maintenance candidate after the CI baseline is settled

A downstream delta check through
`subfish-zhou/goldbach-lean@f688a96b31750c1295ae05db63f88bc80f089154`
found one concrete reuse pattern with existing ANT consumers. Commit
`c222da0a14ffbac061ee930f779fc7046215d2ae` factors duplicated LCM-weight bounds
used by Pan V1/V3 into a shared downstream module. ANT itself still has the
corresponding duplicated finite LCM/harmonic estimates in `PanV1SquareMean.lean`
and `PanV3SquareMean.lean`.

If this refactor is activated after the baseline is green, extract only a neutral
shared helper provable from ANT's existing dependencies and preserve the current
V1/V3 public theorem names as wrappers/aliases where needed. Do **not** copy the
downstream module wholesale: its current implementation imports
`LiLiuPrereqFouvryDivisorMean`, which would pull application-specific Fouvry/Li–Liu
dependencies upstream. Later downstream `LogGridEstimates` and derivative
automation have no named ANT consumer and remain unscheduled.

## Existing results and historical detail

PNT, Mertens II, the exact Mertens product, and the constant-identification chain
remain available; the source and audits are unchanged. Keep the existing
`PrimeNumberTheoremAnd` provenance boundary.

The [previous roadmap](https://github.com/UyNewNas/analytic-number-theory-lean/blob/5536c2d8c387d4bb5438478636c25d7b093206d2/ROADMAP.md)
preserves the earlier release milestones. `PAN_PROOF_ATLAS.md` remains a
historical dependency record; its unchecked items are not all active tasks.
