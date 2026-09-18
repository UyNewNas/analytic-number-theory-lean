import LiuWang.Proof.ExplicitPerron.Series

/-!
# Generic finite Perron series

Stable ANT import boundary for the exact-same-pin generic coefficient-sequence
Perron layer adapted from Liu--Wang.  The source declaration namespace is
intentionally preserved so provenance remains transparent; downstream code
should import this ANT module (or `AnalyticNumberTheory`) rather than the
vendored implementation path directly.

No Dirichlet character, GRH, zero-count, or Mangerel-specific assumption is
introduced here.  See `docs/provenance/perron-series-liu-wang.md`.
-/
