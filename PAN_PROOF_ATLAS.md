# Pan mean-value theorem: proof atlas

> Auditable theorem map for the remaining research-level core of ant issue #7:
> the proof of `AnalyticNumberTheory.Sieve.PanMeanValueUniform` and its bridge
> to `WeightedPanCondition`. This document follows the
> `cross-domain-proof-atlas` workflow and is the review entry point for the
> Pan workline. It is a research instrument, not a catalogue: every node below
> must have a consumer, a verification method, and a stop condition.

## Target and boundary

- **Lean target**: `WeightedPan.PanMeanValueUniform x f` in
  `AnalyticNumberTheory/Sieve/WeightedPan.lean`. As currently written:

  ```text
  ∀ A > 0, ∃ C > 0, ∃ B, ∃ x₀, ∀ X ≥ x₀ :
    ∑_{q ≤ (x X)^{1/2} / log^B (x X)} μ²(q) · 3^{ω(q)} ·
        max_{(l,q)=1} ∑_{a ≤ X} f(a) · |Δ(x X / a; q, l)| ≤ C · x X / log^A (x X)
  ```

  with `Δ(y; q, l) = π(y; q, l) − li(y)/φ(q)` and `π(y; q, l)` the count of
  primes `p ≤ y` with `p ≡ l (mod q)`.

- **Classical target** (Liu 2022, Theorem 2; Pan–Wang–Ding 1975): for every
  fixed `A > 0` there is `B = B(A)` such that

  ```text
  ∑_{q ≤ x^{1/2} log^{-B} x} μ²(q) · 3^{ω(q)} ·
      max_{y ≤ x} max_{(l,q)=1} |∑_{(a,q)=1} f(a) · Δ(y; a, q, l)| ≪ x / log^A x,
  ```

  where `π(y; a, q, l) = #{p : ap ≤ y, ap ≡ l (mod q)}` and
  `Δ(y; a, q, l) = π(y; a, q, l) − li(y/a)/φ(q)`.

- **Claim type**: universal (asymptotic with uniform constants for every
  `A > 0`), for the specific sieve weight `f` (Chen's `p₁p₂` characteristic).
- **Known strongest nearby result in this repository**: the consumption
  interface `WeightedPanCondition` and the finite packaging layer
  (`lcmPairCount`, `lcmPairWeightedSum`,
  `errSum_lambdaSquared_le_threeOmegaWeightedPanRemainder`,
  `selberg_upper_bound_moebius_pan`) are kernel-checked. The analytic core —
  every uniform bound that discharges the weighted remainder — is open.
- **Exact obstruction**: two independent obstructions.

  1. **Infrastructure depth.** mathlib at rev `e4c91783` has Dirichlet
     characters with orthogonality, `ArithmeticFunction` convolution,
     Möbius/von-Mangoldt identities, and Abel summation, but it has **no**
     large-sieve inequality, no mean-value theorem for Dirichlet polynomials,
     and no Vaughan identity. All three are on the critical path and must be
     built here.
  2. **Statement mismatch.** The current Lean target is not the classical
     Pan theorem, and as literally written it is **not true** for the Chen
     weight `f` (see the red-team section below).

## Red-team of the current statement

This is the kind of discrepancy `apply-mathematical-taste` requires us to
name before building machinery around a statement. The current
`PanMeanValueUniform` differs from Liu's Theorem 2 in three ways:

1. **Missing `(a, q) = 1` restriction.** The classical sum is over `(a,q)=1`;
   the Lean sum is over all `a ≤ X`. For `(a,q) > 1` the residue count
   `#{p : ap ≡ l (mod q)}` degenerates (at most one prime solution), so the
   main term `li(x/a)/φ(q)` is **not** cancelled and `|Δ|` is of size
   `li(x/a)/φ(q)`, not `O(x/log^A x)` after summation. With the Chen weight
   `f(a) = 1_{a = p₁p₂}`, the terms with `p₁ | q` or `p₂ | q` sum to
   `≫ x log log x / log x`, which is not `O(x/log^A x)`. This is exactly the
   error in Pan–Wang–Ding that Liu's Section IV corrects. The statement as
   written is therefore false for its intended instantiation.
2. **Missing `max_{y ≤ x}`.** The classical theorem is uniform in the
   truncation `y`; the Lean statement fixes `y = x X`. The Chen switching
   step needs the varying `y = N − a p₃`-type truncations, so the max must be
   present at the seam (or be derived later, but then the derived form is a
   different theorem and must be stated).
3. **Sum of absolute values vs absolute value of sum.** The Lean statement
   bounds `Σ f(a) |Δ(a)|`; the classical one bounds `|Σ f(a) Δ(a)|`. The
   former is stronger and is not what the proof yields at the type-I/II seam.

**Decision (implemented):** restate
`PanMeanValueUniform` to the exact Liu Theorem 2 form (restricted `a`,
`max_y`, inner `|Σ|`), and add the two definitions it needs
(`primesInAPBelow` with an explicit `y` and product congruence, and the
max-over-`y` wrapper `panMaxY`). The
`(a,q) > 1` remainder (Liu's `R₁`) is Chen-specific — it depends on the shape
of `f` and of the sifting product `Q` — so by the repository boundary rule it
belongs in `chen-theorem-lean`, not in ant. The bridge to
`WeightedPanCondition` then consumes the corrected theorem plus the two
standard PNT-level main-term estimates already listed in the ROADMAP.

## Architecture source

- **Landmark proof**: Pan (1963); Bombieri (1965) / A.I. Vinogradov (1965);
  Vaughan (1977). Expositions used as exact-interface sources:
  Halberstam–Richert, *Sieve Methods* (1974) Ch. 10; Liu (2022) §II–III and
  §IV; Iwaniec–Kowalski, *Analytic Number Theory* Ch. 9, 13, 17.
- **Chain architecture** (the classical route to the weighted theorem):

  ```text
  additive large sieve
        | orthogonality of Dirichlet characters (+ Gauss sums)
        v
  multiplicative large sieve
        | Gallagher / Montgomery mean-value device
        v
  mean-value theorem for Dirichlet polynomials
        | Vaughan's identity: Λ = μ ∗ log, split at u, v
        v
  type I / type II bounds  ->  mean-value in AP with weights 3^{ω(q)}
        | Pan weight trick: μ²(q) 3^{ω(q)} = Σ_{d|q} μ²(d) 2^{ω(d)}
        v
  PanMeanValueUniform (classical form) -> WeightedPanCondition (bridge)
  ```

- **Transferable mechanism**: the large-sieve → Vaughan → mean-value chain is
  shared verbatim with Bombieri–Vinogradov and with the future Goldbach
  workline. This justifies building it as *generic* ant infrastructure
  (new `AnalyticNumberTheory/LargeSieve/` layer), not Chen-local.
- **Parity note**: the parity barrier is not an obstruction here — the target
  is a proven mean-value theorem, not a representation problem. The
  breakthrough line below concerns reusable formalization infrastructure,
  not an escape from parity.

## Candidate route (supply line)

Every node has a named consumer. `proven` means kernel-checked in this
repository; `conditional` means an exactly stated assumption; `hypothesis`
means a proposed new bridge that still needs a falsifier.

| Node | Statement or construction | Status | Consumer | Verification / falsifier |
| --- | --- | --- | --- | --- |
| V1 | Vaughan identity: `Λ(n) = Σ_{d\|n,d≤u} μ(d)log(n/d) + Σ_{d\|n,d>u} Σ_{e\|n/d,e≤v} μ(d)Λ(e) + Σ_{d\|n,d>u} Σ_{e\|n/d,e>v} μ(d)Λ(e)` | proven | type I/II split of ψ | `Sieve.VaughanIdentity.vaughanIdentity` |
| V2 | Classical three-term form, valid for `n > v` | proven | BV/Pan type-II extraction | `Sieve.VaughanIdentity.vaughanIdentity_threeTerm` (via `vaughanFullSecondSum`, `vaughanDoubleSum_swap`, `moebiusDivisorSum_eq_ite`) |
| P1 | `Squarefree q → 3^{ω(q)} = Σ_{d\|q} 2^{ω(d)}` | proven | weight absorption in Pan mean value | `Sieve.WeightedPan.threeOmega_eq_sum_twoOmega_divisors` |
| P2 | Double-sum packaging `Σ_q μ²(q)3^{ω(q)}F(q) = Σ_d μ²(d)2^{ω(d)} Σ_m μ²(m)F(dm)` | proven | outer-sum variable change | `Sieve.WeightedPan.threeOmegaWeightedSum_packaging` |
| LS1 | Additive large sieve (Montgomery): `Σ_r \|Σ_n a_n e(n x_r)\|² ≤ (N + δ⁻¹)Σ_n \|a_n\|²` for δ-well-spaced `{x_r}` | hypothesis (next major module) | LS2 | Needs mathlib exponential-sum / circle infrastructure; falsify at δ = 0 |
| LS2 | Multiplicative large sieve: `Σ_{q≤Q} (q/φ(q)) Σ*_χ \|Σ_n a_n χ(n)\|² ≤ (Q²+N)Σ_n \|a_n\|²` | hypothesis | LS3 | Derived from LS1 via `DirichletCharacter` orthogonality + Gauss sums |
| LS3 | Arithmetic form in residue classes | hypothesis | type I bounds | Standard dual reformulation; falsifiable on the `1/q` centering |
| MV | Montgomery mean-value: `∫₀^T \|Σ_{n≤N} a_n n^{-it}\|² dt = (T+O(N))Σ\|a_n\|²` (discrete form via Gallagher) | hypothesis | type I/II | Needs complex integration of Dirichlet polynomials |
| T1/T2 | Type I and type II bounds under `μ²(q)3^{ω(q)}` weights | hypothesis | Pan assembly | Constants must precede `∀ X` |
| PAN | `PanMeanValueUniform` (corrected classical form) | target | `WeightedPanCondition` bridge | Statement must match Liu Thm 2 exactly |
| BRG | Bridge to `WeightedPanCondition` via `li(x) = x/log x + O(x/log²x)` and support truncation | conditional | Chen Ω upper bound | Consumes only the corrected PAN, never the false unrestricted form |

## Dependency sketch

```text
LS1 --[proven? no: hypothesis]--> LS2 --[hypothesis]--> LS3 --[hypothesis]--> MV
                                                                              |
V1 --[target of this cycle]--> V2 --[hypothesis]--> T1/T2 <---[hypothesis]---+
                                                      |
P1 --[target of this cycle]--> P2 --[hypothesis]--> PAN <--[conditional]-- BRG
```

All edges from the analytic layer (LS/MV/T) are `hypothesis` until the
corresponding module exists. The finite layer is kernel-checked: V1, V2, P1,
P2 are all `proven`.

## Next cycle

- **This cycle (done)**: the full finite layer — V1 (`vaughanIdentity`, exact
  for all `n u v`), V2 (`vaughanIdentity_threeTerm` for `n > v`), P1
  (`threeOmega_eq_sum_twoOmega_divisors`), P2
  (`threeOmegaWeightedSum_packaging`) — is kernel-checked, and the corrected
  PAN statement (exact Liu Theorem 2 form) is in place. Full library builds.
- **Smallest next artifact**: the additive large sieve LS1 — Montgomery's
  inequality for δ-well-spaced points, the first module of the new
  `AnalyticNumberTheory/LargeSieve/` layer (the finite layer above is its
  direct consumer once type I/II are attached).
- **Evidence required to retain the route**: V1/P1 must hold at the boundaries
  `n = 1`, `q = 1` and the cutoff extremes `u = 0`, `v = 0` (V1 is stated for
  all of them, so this is discharged); the corrected PAN statement must be
  exactly Liu's Theorem 2.
- **Stop condition**: abandon the current PAN statement if the red-team
  findings cannot be discharged by a restatement; in that case the bridge
  `PanMeanValueUniform → WeightedPanCondition` is invalid and issue #7 must be
  reopened at the interface level.
- **Supply-line connection**: V1/V2/P1/P2 live in
  `AnalyticNumberTheory/Sieve/` (Vaughan identity next to
  `BombieriVinogradov`, weight identities next to `WeightedPan`); LS1–MV are
  reusable and should open a new `AnalyticNumberTheory/LargeSieve/` layer so
  the BV workline can share them.
