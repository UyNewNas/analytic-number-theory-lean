# Half-integer sharp-Perron central-cost reuse audit — 2026-09-23

## Consumer and exact base

Named consumer: `UyNewNas/liouville-reflection-lean`, PR #20, current selected-height Lemma-3.2 path.  The downstream sharp character-Perron bridge uses the canonical nonintegral endpoint `P + 1/2` and currently carries the generic finite `centralCost` explicitly.

ANT base for this extraction is `main@298f8315f9157f495716c44bfb84dcdde8a7e229` (merged #122).  ANT and the selected external source pin the same Mathlib revision `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

## External-first search

Searched before writing:

- pinned Mathlib / mathlib4: supplies `ArithmeticFunction.vonMangoldt_le_log`, harmonic-number bounds, logarithm inequalities, and the finite-sum primitives used below, but no packaged `halfHarmonic` / `centralCost_halfInteger_le` seam;
- canonical `subfish-zhou/goldbach-lean`: no `halfHarmonic` / `centralCost_halfInteger_le` package found;
- `anthropics/formal-math` (zeta23 line, different Mathlib revision): no competing packaged half-integer Perron central-cost theorem found;
- current ANT `main@298f8315...`: already contains the generic dyadic Perron layer, actual-character wrapper, and `twistedMangoldtSequence`, but not the half-integer distance-sum closure;
- exact-same-pin `subfish-zhou/liu-wang-ternary-goldbach-lean@b57b7307810c37267e47110d8b5f920e3e681c81` contains the stronger source chain and is therefore reused rather than re-proved from scratch.

Relevant exact source files / blobs:

- `LiuWang/Proof/ExplicitPerron/HalfInteger.lean` — blob `6d7687aa3410a4d46a3d5132ccf61ee4eb1b4032`;
- `LiuWang/Proof/ExplicitPerron/NearSum.lean` — source theorem `centralCost_halfInteger_le`;
- `LiuWang/Proof/ExplicitPerron/SourceConstants.lean` — blob `4eea6e8db717ee0cdf59b9133c546dca1f79cb00`, source location of the tiny corollary `halfHarmonic_le_log_of_pos`;
- `LiuWang/Proof/ExplicitPerron/ClosedError.lean` — source of the closed logarithmic half-integer error shape;
- `LiuWang/Proof/ExplicitPerron/Characters.lean` — blob `af2b0158a96bb8f288de891de12ba6f54e13eaab`, including `centralCost_twisted_le` and the pointwise chain `‖χ(n)Λ(n)‖ ≤ Λ(n) ≤ log n`.

The source repository is Apache-2.0, consistent with the already-vendored exact-same-pin Perron slices in ANT.

## Dependency-closure decision

The full source `ClosedError.lean` imports `Transport`, `NearSum`, and `SourceConstants`; that closure is larger than the actual downstream need.  The central-cost theorem itself only needs:

`already integrated Dyadic -> HalfInteger -> NearSum`,

plus Mathlib's existing `vonMangoldt_le_log` and ANT's existing character coefficient bound.

`SourceConstants.lean` is deliberately **not** copied.  Its only needed ingredient, `halfHarmonic_le_log_of_pos`, is a one-line consequence of `halfHarmonic_le_log`; the ANT adapter keeps that corollary private instead of importing unrelated printed-constant estimates.  `Transport` is also not needed because the downstream endpoint is already exactly a half-integer.

## Integrated surface on this branch

- provenance-preserving source adaptation of `HalfInteger.lean`;
- provenance-preserving source adaptation of `NearSum.lean`;
- `AnalyticNumberTheory.Dirichlet.characterPerronClosedHalfError`;
- `AnalyticNumberTheory.Dirichlet.centralCost_twisted_halfInteger_le_closed`;
- `AnalyticNumberTheory.Dirichlet.norm_characterPerron_sub_partialSum_le_closed_halfInteger`.

The last theorem keeps ANT's direct finite twisted-von-Mangoldt endpoint.  It does not import the source `characterChebyshevSum`/Vaughan endpoint hierarchy, contour theory, zero counting, GRH, or Liouville/Mangerel parameters.

## Trust gate

The public root imports the new adapter.  `AuditCharacterPerron.lean` is expanded from 6 to 9 fixed reports and the character-Perron augmented public audit from 575 to 578 fixed reports, with the unchanged whitelist `{propext, Classical.choice, Quot.sound}`.

Do not merge or repin downstream until the exact final PR head has a real full root build/trust success and the focused character-Perron audit succeeds on the same SHA.  A runner allocation failure or missing checks is not a green verdict.
