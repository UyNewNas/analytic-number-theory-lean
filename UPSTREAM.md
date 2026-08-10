# Upstream provenance

The implementation modules under `PrimeNumberTheoremAnd/` are a minimal import
closure ported from:

- Project: `AlexKontorovich/PrimeNumberTheoremAnd`
- Release: `v4.32.2`
- Commit: `6a380f0c4658c04a420a9eb00b1ed62a1e3fde01`
- Upstream license: Apache-2.0

## Included roots

- `PrimeNumberTheoremAnd.MediumPNT`
- `PrimeNumberTheoremAnd.Consequences`

Their combined syntactic import closure contains 18 upstream Lean source
files. Files outside that closure are intentionally excluded.

## Local changes

- The package is built against Lean `v4.33.0-rc1` and the exact mathlib
  revision used by `chen-theorem-lean` (`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`).
- `LeanArchitect` is updated to its matching `v4.33.0-rc1` release.
- Stable downstream declarations live under `AnalyticNumberTheory`; consumers
  should not depend directly on the upstream implementation namespace.
- The port is adapted only as needed to compile on the pinned toolchain and to
  expose the stable facade; it is not represented as an independent reproof.
- `Fourier.lean` and `Wiener.lean` use explicit measurability, unit-circle norm,
  and almost-everywhere arguments where Lean 4.33 automation differs.
- Three unused alternate decay lemmas in `Wiener.lean` that contained the only
  executable upstream `sorry` proofs were omitted. They are outside the import
  path of both exported PNT results; the retained proof path is kernel-audited.
- One redundant `rfl` after `simp` was removed from `MediumPNT.lean` for Lean
  4.33 compatibility.

No file outside the 18-file closure is part of this repository's ported proof
surface. The CI trust audit applies to both the ported implementation and the
stable facade.

The original copyright and Apache-2.0 license are retained in `LICENSE`.
