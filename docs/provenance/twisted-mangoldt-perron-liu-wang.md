# Twisted von Mangoldt Perron core provenance

Date: 2026-09-18.

This integration is a bounded external-first reuse/adaptation step for the next sharp character-Perron layer. It is not a new Perron proof line and does not include GRH, zero-counting, Vaughan mean values, Mangerel-specific constants, centered contour assembly, or an application theorem.

## Exact anchors checked before writing

- ANT pinned Mathlib: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
- Canonical Goldbach: `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`.
- Canonical zeta23/formal-math: `anthropics/formal-math@fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` (different Mathlib revision).
- Exact-same-pin Liu--Wang: `subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81`.

The next source wrapper is `LiuWang/Proof/ExplicitPerron/Characters.lean` (blob `af2b0158a96bb8f288de891de12ba6f54e13eaab`). Its source imports are broader than the dependency actually needed for the character-independent norm estimate. We therefore isolate the smallest neutral seam first.

## Reused source material

Two same-pin source files are copied under their original module paths without mathematical edits:

1. `BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/PerronError/Estimate/VonMangoldtLSeries.lean` from the Liu--Wang checkpoint. It defines the positive real-axis von Mangoldt L-series norm sum and identifies its terms/norm with the standard von Mangoldt Dirichlet coefficients.
2. `LiuWang/Proof/ExplicitPerron/Mangoldt.lean` from the same checkpoint. It proves the explicit bound
   `vonMangoldtLSeriesNormSum b ≤ (log 4 + 4) * b / (b - 1)` for `b > 1`, using pinned Mathlib's `Chebyshev.psi_le_const_mul_self` and `LSeries_eq_mul_integral_of_nonneg`.

The public ANT adapter `AnalyticNumberTheory/Dirichlet/TwistedMangoldtPerron.lean` then keeps only the minimal character layer:

- `twistedMangoldtSequence χ n = χ n * Λ(n)`;
- `‖twistedMangoldtSequence χ n‖ ≤ Λ(n)` from `χ.norm_le_one`;
- absolute convergence for `Re(s) > 1` via Mathlib `DirichletCharacter.LSeriesSummable_twist_vonMangoldt`;
- the identity `-L'/L = LSeries (χ·Λ)` as a thin adapter over Mathlib `DirichletCharacter.LSeries_twist_vonMangoldt_eq` plus Mathlib's `LFunction = LSeries` and derivative identities;
- the character-uniform norm-series estimate obtained by comparison with the untwisted Mangoldt bound.

## Explicitly not reused here

- The source `PerronError/Estimate/Coefficient.lean` also proves a full Perron-majorant comparison. The present integration needs only its elementary coefficient inequality, so importing the complete majorant hierarchy would be over-broad.
- The source `Characters.lean` defines its endpoint through `characterChebyshevSum`, which imports a Vaughan-mean-value hierarchy. The future ANT wrapper should instead use the finite endpoint sum directly unless an independent consumer needs that larger API.
- The source `LFunctionLogDerivativeRightHalfPlaneBound` import is not brought in here. The identity needed at this stage is already a Mathlib-backed L-series identity; any explicit `-L'/L` norm wrapper beyond absolute convergence must be justified separately.
- zeta23 remains prior art for broader Dirichlet-character contour/zero machinery but is on a different Mathlib revision and is not a drop-in dependency for this same-pin sharp Perron seam.

## Intended next consumer

After this core has exact build and axiom-audit evidence, the next bounded step is a sharp character-Perron wrapper that combines it with the already-integrated generic dyadic Perron theorem from PR #95. `Centered` remains a later, separate justification. Project-specific Liouville/Mangerel statements remain downstream in `UyNewNas/liouville-reflection-lean`.
