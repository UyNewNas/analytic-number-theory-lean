# Maintenance and reuse roadmap

Direction adopted 2026-09-14; status refreshed 2026-09-16. The library retains
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

This source comparison has produced a bounded neutral ANT implementation; it is
not a second Chen application project. Existing
[PR #70](https://github.com/UyNewNas/analytic-number-theory-lean/pull/70), current
head `299836966ed5f953cf2b00673ee570524d2813b3`, preserves the public convention

```text
primeLogIntegral(x) = integral from 2 to x of 1/log(t),
primeLogIntegral(2) = 0.
```

The pinned downstream
[`Arithmetic/LiuLogarithmicIntegral.lean`](https://github.com/subfish-zhou/goldbach-lean/blob/df1f3b3b721c9a0b5e38ba39d5c0e3c2a1d72f59/MathlibNt/SieveTheory/Arithmetic/LiuLogarithmicIntegral.lean)
uses

```text
liuLogarithmicIntegral(kappa, x) = kappa + integral from 2 to x of 1/log(t).
```

The exact pinned-source normalization bridge is now machine-verified. Temporary
verification commit `a937f8ebb713c08d7c8305698e55a1b5e2f7c111` checked out
`goldbach-lean@df1f3b3b...`, extracted that exact declaration from the pinned
source, compiled it against ANT's `primeLogIntegral`, and proved

```text
liuLogarithmicIntegral kappa x = kappa + primeLogIntegral x
```

by definitional equality. Workflow run
[`35053020347`](https://github.com/UyNewNas/analytic-number-theory-lean/actions/runs/35053020347)
(run #311) completed **success** for the repository build, pinned-source bridge,
focused genuine-Li audit, and repository-wide public theorem axiom audit. This is
stronger than source inspection but deliberately narrower than importing or
compiling the full downstream Goldbach/Liu application project. No
`LiuWeightPaperQ` or application dependency was added to ANT.

The one-off downstream-network probe was removed in cleanup commit
`299836966ed5f953cf2b00673ee570524d2813b3`; ordinary workflow run
[`35053222263`](https://github.com/UyNewNas/analytic-number-theory-lean/actions/runs/35053222263)
(run #312) completed **success** on that current head. Thus the bridge evidence is
retained without making `goldbach-lean` a permanent ANT dependency or CI input.

PR #70 contains the neutral slice required by #69:

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

The independent Bombieri–Davenport baseline repair
[PR #73](https://github.com/UyNewNas/analytic-number-theory-lean/pull/73) was merged
into `dev` as `b326ecbe03daf16916e9f3f9f632c45eeef6aa32`. PR #70 was then synchronized
non-forced to that repaired baseline.

Combined workflow run
[`34923846194`](https://github.com/UyNewNas/analytic-number-theory-lean/actions/runs/34923846194)
(run #300) completed **success** on the repaired-baseline PR #70 state. The executable
`sorry`/`admit` scan, repository-wide Lean build, focused `Audit genuine Li slice`,
and repository-wide public theorem axiom audit all passed. Runs #311 and #312 add
the pinned-source normalization evidence and confirm that removing the temporary
probe leaves the ordinary audit regime fully green.

The old pre-integration Bombieri–Davenport failure is therefore historical only.
Issue #71 is completed and diagnostic-only PR #72 is closed unmerged. PR #70 is
integration-ready from the currently required build/trust perspective, but remains
open and unmerged.

### Dormant stronger interfaces

Do not continue automatically from the neutral `O(x/log^2 x)` result to arbitrary
fixed logarithmic saving, `WeightedBVAtOne`, supported transport, or a general Pan
theorem. Activate one only when a named consumer requires the exact statement and
the source/type comparison matches its weights, support, main term, level, maxima,
and quantifier order.

## Second bounded maintenance slice: neutral LCM de-duplication (PR #75)

A downstream delta check through
`subfish-zhou/goldbach-lean@f688a96b31750c1295ae05db63f88bc80f089154`
identified a concrete proof-reuse pattern with existing ANT consumers. Downstream
commit `c222da0a14ffbac061ee930f779fc7046215d2ae` factors duplicated LCM-weight
bounds used by Pan V1/V3. ANT implemented the analogous refactor locally without
copying downstream application dependencies.

[PR #75](https://github.com/UyNewNas/analytic-number-theory-lean/pull/75), head
`9ff29473a55044b0e26a2cabf29c0af59142105c`, adds an ANT-native neutral shared
layer for:

- `LcmWeightBounds.harmonic_Icc_le`;
- `LcmWeightBounds.card_multiples_Icc`;
- `LcmWeightBounds.lcm_inv_sum_le`;
- `LcmWeightBounds.divisorCountSq_sum_le`.

The existing V1 public names `harmonic_Icc_le`, `card_multiples_Icc`,
`lcm_inv_sum_le`, and `divisorCountSq_sum_le` are preserved as thin wrappers. The
existing V3 public names `v3_harmonic_Icc_le`, `v3_card_multiples_Icc`,
`v3_lcm_inv_sum_le`, and `v3_divisorCountSq_sum_le` are likewise preserved.
`Audit.lean` continues to audit both families, `W1Assembly` still consumes
`v3_card_multiples_Icc`, and `NonCoprimeDensity` still consumes the unprefixed
`divisorCountSq_sum_le`.

The shared layer depends only on ANT/Mathlib-neutral inputs; no downstream
`LiLiuPrereqFouvryDivisorMean`, Li–Liu application code, weighted-BV theorem, or
general-Pan specialization was imported. Across the two Pan files the conversion
removes roughly 900 lines of duplicated proof implementation while retaining all
public declarations.

Incremental runs #302 through #306 were green. Final workflow run
[`35021692159`](https://github.com/UyNewNas/analytic-number-theory-lean/actions/runs/35021692159)
(run #307) completed **success** on the exact PR #75 head for the executable
`sorry`/`admit` scan, repository-wide Lean build, and public theorem axiom audit.
PR #75 is ready for review, mergeable, and remains unmerged; merge is an explicit
owner decision.

## Independent demand-backed reuse lane: Dirichlet core (PR #76)

A separate downstream consumer, `UyNewNas/liouville-reflection-lean`, now provides
a concrete reason to extract project-neutral Dirichlet infrastructure into ANT.
This is not a continuation of the Goldbach/Li/Pan maintenance slice and does not
reactivate the retired Chen-completion programme.

[PR #76](https://github.com/UyNewNas/analytic-number-theory-lean/pull/76), current
observed head `be8d8927c51d636a74f85f38527d56ffa5cafc45`, provides neutral GRH,
character orthogonality/decomposition, and exact finite weighted second-moment
interfaces while leaving Liouville defects, Mangerel-specific parameters, and
application theorem statements downstream. Workflow run
[`35078861322`](https://github.com/UyNewNas/analytic-number-theory-lean/actions/runs/35078861322)
(run #355) completed **success** on that exact head: executable `sorry`/`admit`
rejection, repository-wide Lean build, repository-wide public theorem axiom audit,
and the focused 20-declaration reusable Dirichlet audit all passed.

This roadmap records #76 because it is a real demand-backed ANT reuse lane and
therefore changes the repository integration topology. The Goldbach/Li maintenance
plan does not take ownership of, rewrite, or broaden that PR. Its merge remains an
explicit owner decision.

## Current engineering stop

There is no further **Goldbach/Li/Pan maintenance** code slice in the current work
register that simultaneously has a named ANT consumer and an already-audited exact
type boundary. Later downstream `LogGridEstimates` and derivative automation still
have no named ANT consumer and remain unscheduled. Do not manufacture stronger
pi-Li, weighted BV, supported transport, or general Pan work merely because PR #70
and PR #75 are green.

A separate named-consumer lane is active in PR #76 and is independently green.
Current repository-state decisions are therefore integration decisions for the
green `dev` code PRs (#70, #75, and #76) plus this distinct `main`-based
documentation PR (#74). Because `main` and `dev` are diverged, the documentation
CI does not substitute for a hypothetical combined `dev` tree. Maintenance should
resume with another Goldbach/Li/Pan code slice only when a concrete consumer or
exact required interface is identified.

## Existing results and historical detail

PNT, Mertens II, the exact Mertens product, and the constant-identification chain
remain available; the source and audits are unchanged. Keep the existing
`PrimeNumberTheoremAnd` provenance boundary.

The [previous roadmap](https://github.com/UyNewNas/analytic-number-theory-lean/blob/5536c2d8c387d4bb5438478636c25d7b093206d2/ROADMAP.md)
preserves the earlier release milestones. `PAN_PROOF_ATLAS.md` remains a
historical dependency record; its unchecked items are not all active tasks.
