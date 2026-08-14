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

**RHS correction on the main-term sub-chain (ant #15, line T3i, after PR #41):**
the old `PanMainSieveAbsorption`/`PanMainTermSieveBound`/`PanMainTermBound`
claimed `C·xX/log^A(xX)` for the `li` principal piece alone. That is false as
a single inequality even for the typical instance `x X = X` (LHS ≈ `X·log⁷X`,
RHS ≈ `C·X/log^A X`; the classical bound is a *difference* bound after the
sieve main term is subtracted). The repo now states the honest provable content:
a fixed polylog factor is eventually dominated by any larger power of `log`
(`PanMainSieveAbsorption` is proved in `PanMainTerm.lean` §6.1 as
`xX·(1+log X)·log⁶(xX+2) ≤ C·xX·(log xX)^{A+7}` for `X ≤ x X`, C = 128), and
the RHS of the whole main-term sub-chain (and hence of `PanVaughanSplit` /
`PanMeanValueUniform`) is the polylog form `C·xX·(log xX)^{A+7}`. The
classical `C·x/log^A x` form remains the open BRG target (sieve-main-term
subtraction, out of scope for this chain).

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
| LS1 | Additive large sieve (Montgomery): `Σ_r \|Σ_n a_n e(n x_r)\|² ≤ (N + δ⁻¹)Σ_n \|a_n\|²` for δ-well-spaced `{x_r}` | proven with explicit weak constant, ℝ version (`LargeSieve/WellSpaced.lean`: `wellSpacedRowSum` dyadic-shell row sum + `quadraticFormBound` Schur/CS test yield `largeSieveDual_wellSpaced`/`largeSievePrimal_wellSpaced` with constant `C(N,δ) = N + (2⌈log₂(1/δ)⌉+12)/δ`; counting lemmas `sepCard_le_interval`, `wellSpaced_ball_card_le`; kernel-checked). Strong constant `N + δ⁻¹` is an open dependency (needs positive-definite kernel device). The `AddCircle 1` statement (`MontgomeryLargeSievePrimal/Dual`) needs the real↔circle bridge (representative lift + `dist = distToInt`) | LS2 | Bridge the ℝ theorem to the `AddCircle 1` statement via `AddCircle.liftIco`/`dist` lemmas, then derive the multiplicative large sieve via `DirichletCharacter` orthogonality |
| LS2 | Multiplicative large sieve: `Σ_{q≤Q} (q/φ(q)) Σ*_χ \|Σ_n a_n χ(n)\|² ≤ (Q²+N)Σ_n \|a_n\|²` | 组件已 kernel-checked，最终装配开放（`LargeSieve/Multiplicative.lean`: 特征正交性 `charOrthSum`/`charOrthogonality_le`（全部特征，mathlib `sum_char_inv_mul_char_eq`）、逆 Parseval `zmodParseval_inv`、字符版 Parseval `zmodParseval_character`、Farey 点集加法大筛 `largeSieveRationalPoints`（常数 `largeSieveBound N (1/Q²)`）、模 `q` 点式特征大筛 `characterSieveModulus_le`。**红队修正**: 原设计想对带重数点集 `Σ_{q≤Q} Σ_{r<q} \|S(r/q)\|²` 做加法大筛——该路线不成立（反例 `a_n≡1`, `N` 大, `Q=2`）；经典 Bombieri–Davenport 形式需要**原特征** + Gauss 和（`(q/φ(q))\|S(χ)\|² = (1/φ(q))\|Σ_{(a,q)=1} conj(χ(a))S(a/q)\|²`）与既约分数对求和，故原特征版本保留为开放目标 | LS3 | 在原特征/Gauss 和装置就绪后装配经典形式；`characterSieveModulus_le` 提供点式输入 |
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
- **This cycle (done)**: the geometric-sum bound is kernel-checked
  (`LargeSieve/GeomSum.lean`): `|Σ_{n<N} e(nx)| ≤ min(N, 1/(2‖x‖))` in two
  parts — trivial `≤ N` (each term has norm 1) and nontrivial
  `≤ 1/(2‖x‖)` via the geometric-series identity, the trigonometric identity
  `|e(x)−1| = 2|sin(πx)|`, and the sin lower bound
  `|sin(πt)| ≥ 2·min(t, 1−t)`; the distance-to-integer `‖x‖` uses
  `Int.fract`/`Int.floor`.
- **This cycle (done)**: the interval geometric-sum bound
  (`geomSum_exp_bound_Icc` via `charRealSubIcc_eq_shift`, `e((M+1)x)`-factor)
  and the dual quadratic-form identity (`LargeSieve/Duality.lean`:
  `dualExpansion` for finite matrices, then `dualQuadraticIdentity` /
  `dualQuadraticIdentity_Icc` / `dualQuadraticIdentity_circle` via the
  character-cross lemmas `charReal_cross` / `charPow_cross`) are
  kernel-checked. The circle version matches the `MontgomeryLargeSieveDual`
  statement exactly, so the Parseval seam of LS1 is now fully formal.
- **This cycle (done)**: the well-spaced/Schur step that closes LS1 in its
  ℝ-parameterized form (`LargeSieve/WellSpaced.lean`). Counting: an interval
  of length `L` contains at most `L/δ + 1` pairwise `δ`-separated points
  (`sepCard_le_interval`, max-point induction), which yields the mod-1 ball
  count `#{y : distToInt(x−y) ≤ r} ≤ 2r/δ + 2` for `r ≤ 1/2`
  (`wellSpaced_ball_card_le`). Row sum: dyadic shells with the geometric-sum
  bound give `Σ_{y∈X} |Σ_{M<n≤M+N} e(n(x−y))| ≤ N + (2K+12)/δ` with
  `K = ⌈log₂(1/δ)⌉` (`wellSpacedRowSum`). Schur/CS: Hermitian symmetric
  kernels with row sums ≤ C bound the dual quadratic form by `C·Σ|b_x|²`
  (`quadraticFormBound`). Assembly: `largeSieveDual_wellSpaced` and
  `largeSievePrimal_wellSpaced` (constant `C(N,δ) = N + (2⌈log₂(1/δ)⌉+12)/δ`,
  the primal form via `largeSieveDuality`). **Constant honesty**: the strong
  constant `N + 1/δ` needs Montgomery's positive-definite kernel/Parseval
  device; a plain Schur test is structurally limited to a `log(1/δ)`-loss
  weak constant (dyadic shells + Schur row sums), and the sharp constant is
  recorded as an open dependency (needs additional Fourier-kernel
  infrastructure, e.g. the Fejér-kernel majorant `|D_N|²/N`).
- **Smallest next artifact**: bridge the ℝ theorem to the `AddCircle 1`
  target statements `MontgomeryLargeSievePrimal/Dual` — choose a
  representative `rep : AddCircle 1 → ℝ` (e.g. `AddCircle.liftIco`),
  prove `dist (mk a) (mk b) = distToInt (a−b)` and the character
  compatibility `charPow n (mk z) = charReal (n·z)`, then transport
  `largeSievePrimal_wellSpaced`/`largeSieveDual_wellSpaced` to the circle.
  Afterwards the multiplicative large sieve LS2 via `DirichletCharacter`
  orthogonality.
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

## Body workline (ant #15): proof route and status

> Branch `research/pan-mean-value-body`. The route below is the concrete
> lemma-by-lemma plan for proving `PanMeanValueUniform` (the PAN node),
> mapping each step to existing infrastructure or to an explicitly recorded
> open lemma. Chinese annotations per the workline convention.

### Route (Liu 2022 §II--§III, Halberstam--Richert Ch.10)

```text
PAN statement (WeightedPan.lean)
  │  [B1] max removal: panMaxY ≤ Σ_y Σ_l |panDistributionSum|      ← DONE (B)
  │  [A ] a-absorption: panDistributionSum = weighted AP-error sum  ← DONE (A)
  │  [P2] 3^ω(q) = Σ_{d|q} 2^ω(d) repackaging                      ← existing (WeightedPan)
  v
weighted AP-error sum  Σ_{(a,q)=1} f(a)·(π(y/a;q,la⁻¹) − li(y/a)/φ(q))
  │  [V ] Vaughan identity on the AP prime count (Λ = μ∗log)        ← existing (VaughanIdentity)
  │  [C ] character expansion of the AP indicator (orthogonality)   ← open (needs sum_char_inv_mul_char_eq assembly)
  v
type I  (small factors)   ← [T1] OPEN: weighted large-sieve/BV-type bound
type II (bilinear)        ← [T2] OPEN: mean value at Farey points, bilinear form
main term (li sums)       ← [T3] OPEN: PNT-level li(y/a) main-term estimate
  │
  v
PAN: Σ_q μ²(q)3^ω(q)·panMaxY ≤ C·x/log^A x      (assembly of T1+T2+T3 with B1, A, P2)
```

### Status of the current cycle (branch research/pan-mean-value-body)

- **[A] a-absorption — DONE (kernel-checked)**: `Sieve/PanMeanValueBody.lean`
  Sections 1--2. `natInvMod` (least inverse residue), `modEq_mul_left_inv_iff`
  (coprime multiplication cancels in `ModEq`), `primesInAPBelow_eq_primesInAP_inv`
  (scaled count = plain AP count at `y/a`), `panDistributionError_scaled_inv`,
  and the Liu §II weighted form `panDistributionSum_eq_weighted` (the a=0 term
  is split off explicitly; it is nonzero only for q = 1).
- **[B1] max scaffolding — DONE (kernel-checked)**: Section 3.
  `panMaxL_nonneg`, `panMaxY_le_sum`, `panMaxL_le_sum_abs`,
  `panMaxY_le_sum_abs` (double max ≤ double sum).
- **Next smallest artifacts**: (C) the AP-indicator character expansion
  `Σ_χ χ(n)·conj(χ(l)) = φ(q)·1_{n≡l}` for units (via
  `DirichletCharacter.sum_char_inv_mul_char_eq` already used in
  `charOrthSum`), then (T1/T2) the type I/II bounds consuming
  `largeSieveRationalPoints` / `characterSieveModulus_le` / Vaughan.

### Open lemmas (recorded as Prop defs in PanMeanValueBody.lean §4, sources cited)

| Tag | Statement (def) | Source | Needed by |
| --- | --- | --- | --- |
| T1 | `PanTypeIWeightedBound` — weighted type-I estimate at level `Q = x^{1/2}/log^B x` | Liu §III Lem.1; HR 1974 Ch.10 | PAN assembly |
| T2 | `PanTypeIIWeightedBound` — bilinear type-II estimate | Liu §III; Montgomery mean value | PAN assembly |
| T3 | `PanMainTermBound` — li(y/a) main-term sums | PNT (PrimeDistribution) | PAN assembly |

### Evidence / stop conditions

- A is exact for all `y,a,q,l` with `(a,q)=1, a ≥ 1` (no analytic input);
  B1 is exact finite combinatorics.
- T1/T2 need the large-sieve constants of LS1/LS2; the strong constant
  `N + δ⁻¹` remains an open dependency (see LS1 note above).
- Stop condition unchanged from the PAN node: if the (a,q)=1-restricted
  statement cannot be discharged by this route, the bridge to
  `WeightedPanCondition` must be re-audited (issue #7).

