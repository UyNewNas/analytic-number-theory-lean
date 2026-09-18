# Smoothed Perron downstream consumer closure

Date: 2026-09-18.

## Consumer break found after the von-Mangoldt window merge

After ANT PR #98 merged at `main@24c62281ed3a1ba8b5c6dc2d2dc5f2f1a8e594fe`, `UyNewNas/liouville-reflection-lean` correctly repinned its ANT dependency to that stable main SHA. A fresh dependency audit of the current LR root then exposed a separate older dependency surface that PR #98 did not claim to restore.

Current LR `formalize/core-and-energy-completion` still root-imports its smoothed-Perron application modules. In particular:

- `MangerelVonMangoldtInterface.lean` imports `AnalyticNumberTheory.Dirichlet.VonMangoldtLSeries`;
- `MangerelTwistedSmoothedPerron.lean` imports `AnalyticNumberTheory.Dirichlet.TwistedSmoothedPerronRightTail`;
- the horizontal / vertical / contour wrappers import the corresponding neutral ANT smoothed-Perron modules;
- `MangerelTwistedSmoothedPsiUnsmoothing.lean` imports `AnalyticNumberTheory.Dirichlet.TwistedSmoothedPsiCloseUniform`.

Those modules are present on the old verified `reuse/dirichlet-core-20260916` lane but are not all present on current ANT main. Repeated LR Actions failures with `runner_id=0` and `steps=[]` happened before checkout and therefore did not test this dependency closure.

This is an integration/dependency defect, not evidence against any mathematical theorem in LR.

## Prior art and source anchors

The smoothed Perron modules on the old ANT lane are provenance-preserving extractions from canonical same-mathlib-pin work in `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`, including its genuine twisted smoothed Perron inversion and character-neutral contour estimates. The old ANT lane kept the application-neutral statements and was repeatedly built/audited there.

The current ANT main also contains the newer exact-same-pin Liu--Wang sharp-Perron extraction (`TwistedMangoldtPerron`, `CharacterPerron`). That newer sharp layer does not by itself satisfy the old smoothed API imported by LR, and the LR smoothed proofs remain root-reachable. We therefore do not delete those downstream proofs merely to make the dependency graph smaller.

## Minimal integration plan

Do not repin LR back to the 260-commit diverged #76 lane and do not merge #76 wholesale. Restore the consumer closure to current ANT main in bounded slices:

1. restore the historical `VonMangoldtLSeries` compatibility/analytic seam required by `MangerelVonMangoldtInterface` and verify it freshly on current main;
2. restore only the neutral smoothed Perron modules actually imported by the LR root (`TwistedSmoothedPerron`, right/right-tail, horizontal, vertical, contour, and the two smoothing-removal modules), preserving source provenance;
3. add a focused placeholder/axiom audit and require the normal full ANT build/audit on the current-main branch;
4. only after the complete slice is green should LR remain pinned to the resulting merged main SHA and be considered dependency-closed. LR itself still requires a real downstream build/audit; pre-runner Actions failures are not a verdict.

The first slice in this branch restores `AnalyticNumberTheory.Dirichlet.VonMangoldtLSeries` from the previously verified neutral implementation. It is intentionally not treated as completion of the full smoothed-Perron closure.
