# Dirichlet local-zero consumer bounds provenance

Date: 2026-09-21

Named consumer: `UyNewNas/liouville-reflection-lean`, Mangerel/Dirichlet-character local-zero and selected-height path.

## External-first audit

Pinned Mathlib is `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.  Current stable ANT already contains `AnalyticNumberTheory.Dirichlet.norm_LFunction_le_growth`, proved from the same-pin conditional-series layer, so no Mellin/analytic-continuation tree is copied.

Different-revision prior art is `anthropics/formal-math@fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`, `zeta23/Zeta23/ThmE/LGrowth.lean`, notably `LFunction_growth_right_uniform`, `norm_LFunction_sub_one_le`, `LFunction_lower_bound_two`, and `LFunction_ne_zero_of_two_le_re`.  The source's broad positive-half-plane route imports its own Mellin/growth support and is not a drop-in dependency at ANT's pinned revision.

Canonical same-revision `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958` was also checked during the original extraction; no competing packaged Jensen-centre `1/3` theorem was found there.

## Existing verified implementation recovered, not re-invented

The exact neutral theorem bodies already existed on historical ANT PR #76 (`reuse/dirichlet-core-20260916`):

- `AnalyticNumberTheory/Dirichlet/LFunctionGrowthUniform.lean::norm_LFunction_le_growth_right_uniform`;
- `AnalyticNumberTheory/Dirichlet/LFunctionTwoBounds.lean::{norm_LFunction_sub_one_le_of_two_le_re, one_third_le_norm_LFunction_of_two_le_re, LFunction_ne_zero_of_two_le_re}`.

Those modules had exact-head build/axiom verification on the long-lived integration lane, but they were not present on current stable `main@7c61e558a78870105777f42324fc3c4baee38e18`.  LR had retained imports of them while repinning to current stable ANT, so the stable dependency graph had become source-incomplete even though LR Actions were failing before runner assignment and therefore did not expose the compile error.

This restoration keeps the original theorem bodies, updates provenance to the accessible zeta23 repository/commit, imports them from the stable ANT root, and adds a dedicated four-declaration trust audit.  No GRH, Liouville object, Mangerel parameter, contour, zero-count, or application-specific statement enters ANT.

## Verification boundary

The historical verification is provenance, not a verdict for the restored current-main tree.  The restoration is consumable by LR only after the new exact PR head completes its own Lean build and dedicated axiom audit under the repository whitelist `propext / Classical.choice / Quot.sound`, followed by stable integration according to the normal ANT merge rules.
