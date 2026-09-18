# Smoothed Perron downstream consumer closure

Date: 2026-09-18.

## Consumer break found after the von-Mangoldt window merge

After ANT PR #98 merged at `main@24c62281ed3a1ba8b5c6dc2d2dc5f2f1a8e594fe`, `UyNewNas/liouville-reflection-lean` correctly repinned its ANT dependency to that stable main SHA. A fresh dependency audit of the current LR root then exposed a separate older dependency surface that PR #98 did not claim to restore.

Current LR `formalize/core-and-energy-completion` still root-imports its smoothed-Perron application modules. In particular:

- `MangerelVonMangoldtInterface.lean` imports `AnalyticNumberTheory.Dirichlet.VonMangoldtLSeries`;
- `MangerelTwistedSmoothedPerron.lean` imports `AnalyticNumberTheory.Dirichlet.TwistedSmoothedPerronRightTail`;
- the horizontal / vertical / contour wrappers import the corresponding neutral ANT smoothed-Perron modules;
- `MangerelTwistedSmoothedPsiUnsmoothing.lean` imports `AnalyticNumberTheory.Dirichlet.TwistedSmoothedPsiCloseUniform`.

Those modules are present on the old verified `reuse/dirichlet-core-20260916` lane but were not all present on current ANT main. Repeated LR Actions failures with `runner_id=0` and `steps=[]` happened before checkout and therefore did not test this dependency closure.

This is an integration/dependency defect, not evidence against any mathematical theorem in LR.

## Prior art and source anchors

The smoothed Perron modules on the old ANT lane are provenance-preserving extractions from canonical same-mathlib-pin work in `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`, including its genuine twisted smoothed Perron inversion and character-neutral contour estimates. The old ANT lane kept the application-neutral statements and was repeatedly built/audited there.

The current ANT main also contains the newer exact-same-pin Liu--Wang sharp-Perron extraction (`TwistedMangoldtPerron`, `CharacterPerron`). That newer sharp layer does not by itself satisfy the old smoothed API imported by LR, and the LR smoothed proofs remain root-reachable. We therefore do not delete those downstream proofs merely to make the dependency graph smaller.

## Bounded integration plan

Do not repin LR back to the 260-commit diverged #76 lane and do not merge #76 wholesale. Restore the consumer closure to current ANT main in bounded slices:

1. restore the historical `VonMangoldtLSeries` compatibility/analytic seam required by `MangerelVonMangoldtInterface` and verify it freshly on current main;
2. restore only the neutral smoothed Perron modules actually imported by the LR root (`TwistedSmoothedPerron`, right/right-tail, horizontal, vertical, contour, and the two smoothing-removal modules), preserving source provenance;
3. add a focused placeholder/axiom audit and require the normal full ANT build/audit on the current-main branch;
4. only after the complete slice is green should LR remain pinned to the resulting merged main SHA and be considered dependency-closed. LR itself still requires a real downstream build/audit; pre-runner Actions failures are not a verdict.

## Current branch progress

Phase 1 restored `AnalyticNumberTheory.Dirichlet.VonMangoldtLSeries` and its compatibility audit. At head `037f21e9ea8d9a268c408303c51969d87279842e`, all ten pull-request workflows completed successfully, including the normal full `Lean build and trust audit` and the focused von-Mangoldt L-series compatibility audit.

Phase 2 now restores exactly the old verified neutral blobs required by the root-reachable LR smoothed-Perron consumer surface, from `reuse/dirichlet-core-20260916@3648560407c1c6deee7d2f7fe7f2acad95a924fd`:

- `TwistedSmoothedPerron.lean` (`704c6a21895de9a2f2578fbb5e3f47f03c1ef27e`)
- `TwistedSmoothedPerronRight.lean` (`d52bfdf3f621dbdcd4f5bddfa04ab937f2baa5fe`)
- `TwistedSmoothedPerronRightTail.lean` (`66af71e55f1ee0eb4e2c1a369e7b8368df3f3a47`)
- `TwistedSmoothedPerronHorizontal.lean` (`c9878747703a7386de48e14d0dff9dbe710a1de9`)
- `TwistedSmoothedPerronVertical.lean` (`f34cb90383adc8ca47421b2c85f24bbf801f5df9`)
- `TwistedSmoothedPerronContour.lean` (`a785413a6b2763c0172eaa575b5a48bb99264733`)
- `TwistedSmoothedPsiClose.lean` (`9ca2e2c81e4aeac667dc03d4463be242f2f43b13`)
- `TwistedSmoothedPsiCloseUniform.lean` (`2f31fa7a74ab18333ad7e5991919acf8a41b23f5`)

The public root imports the restored slice so the ordinary full build cannot silently skip it. `AuditPerron.lean` is restored from the same verified lane, and `.github/workflows/smoothed-perron-consumer-audit.yml` rejects `sorry`/`admit`, compiles the public root, and checks sixteen public theorem axiom reports against the repository whitelist `{propext, Classical.choice, Quot.sound}`.

This phase is not considered complete until the resulting branch head has fresh successful pull-request workflow results. A green historical #76 build is provenance evidence only, not current-main verification.
