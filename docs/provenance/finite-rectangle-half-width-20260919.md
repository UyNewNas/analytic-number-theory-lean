# Finite-rectangle `δ ≤ 1/2` provenance and consumer audit

Date: 2026-09-19

Named consumer: `UyNewNas/liouville-reflection-lean`, direct sharp-dyadic contour at left edge `Re s = 1/4`.

## Existing source baseline

ANT's `FiniteRectangleLogDerivative.lean` was adapted from
`subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`,
`MathlibNt/AnalyticNumberTheory/DirichletL/DirichletLZeroFreeFiniteRectangleLogDerivative.lean`.
That source states `δ ≤ 1/4` and therefore only reaches target real parts
`β ≥ 1-δ/2 ≥ 7/8`.

The exact-same-Mathlib Liu--Wang source
`subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`
has a quantitative two-sided good-height theorem on horizontal lines and a
functional-equation left-line bound at `Re s=-1/2`; the latter reflects to
`Re(1-s)=3/2`. It does not package the required all-heights vertical bound at
`Re s=1/4` or an arbitrary-left-line reflection theorem.

`anthropics/formal-math@fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`,
`zeta23/Zeta23/ThmE/LandauChi.lean::L_logDeriv_partial_fraction`, supplies a
more general local partial-fraction mechanism around `2+it`. It is relevant
prior art for controlling points such as `3/4+it` under a zero-location input,
but it lives on a different Mathlib revision and is not a drop-in theorem for
ANT's pinned environment. No same-shaped packaged `β=3/4` GRH bound was found
in the audited sources.

## Why the existing ANT proof itself extends to `δ ≤ 1/2`

No complex-analytic theorem or constant changes. Only the range hypotheses on
the existing neutral anchor geometry are widened.

For the anchor disk centered at `1+δ/2+it` with radius `3δ/2`:

- its left edge is **strictly** to the right of `1-δ`, hence for `δ≤1/2` it remains
  in `Re s>1/2`;
- its right edge is below `1+2δ≤2`;
- its imaginary displacement is `<3δ/2≤3/4<1`, so the finite rectangle with
  height margin `T+1` still contains it;
- the existing conditional-series growth argument needs only `Re w≥1/2` and
  the same norm envelope `‖w‖≤2+|t|`, both still follow from `δ≤1/2`;
- the product-anchor estimate `δ/4≤‖L(1+δ/2+it,χ)‖` uses the majorant
  `1+2/δ≤4/δ`, which remains valid throughout this wider range.

The strict first bullet matters at the endpoint `δ=1/2`: a GRH application may
have zeros on `Re s=1/2`, so requiring a **closed** zero-free rectangle from
`Re s=1/2` would be unnecessarily false even though the open anchor disk never
touches that line.

## API shape in this PR

The existing closed-rectangle theorem is preserved as a compatibility wrapper
and its width is widened to `δ≤1/2`.

A new neutral theorem

`norm_logDeriv_LFunction_le_of_zeroFree_openLowerRectangle`

uses the exact hypothesis required by the proof:

`1-δ < Re z ≤ 2`, `|Im z|≤T+1`.

The open-lower theorem performs the actual small-disk argument using
`anchor_disk_re_lower`; the previous closed theorem delegates to it by weakening
`<` to `≤`. This keeps old consumers compatible while making the endpoint
`δ=1/2` usable under a zero-free open half-plane such as GRH.

`AuditDirichletLogDerivative.lean` now includes the new public theorem in the
focused axiom audit.

## Consumer consequence, once kernel-verified

At `δ=1/2`, the open-lower theorem reaches `β=3/4`, while requiring nonvanishing
only for `Re s>1/2`. That hypothesis matches the existing ANT/LR GRH half-plane
zero-free theorem without excluding legitimate critical-line zeros.

The Liouville consumer would then need only a thin GRH specialization at
`β=3/4` plus a source-audited functional-equation reflection transferring the
`3/4` estimate to the desired `1/4` line. The present PR does **not** prove that
reflection or any Mangerel-specific statement.

## Validation status

The branch changes remain unverified until the **latest exact head** completes
the ANT root build and focused/public axiom audits. Earlier runs for superseded
heads are not evidence for the final API. Do not consume the widened range
downstream before that verdict.