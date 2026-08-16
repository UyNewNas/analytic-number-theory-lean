# Formal Mathematics Atlas roadmap

This repository is the reusable **Prime Distribution / Analytic Number Theory**
foundation. It is upstream of theorem-focused repositories such as Chen and
future Goldbach developments.

```text
analytic-number-theory-lean
├── prime distribution (PNT and effective psi estimates)
├── Mertens II and canonical product asymptotics
└── Abelian constant-identification bridge
        │
        ├──> chen-theorem-lean (sieve consumer)
        ├──> goldbach-lean (future)
        └──> other prime-distribution consumers
```

## Release lines

### v0.1 — prime-distribution foundation

- [x] Pin the Chen-compatible Lean/mathlib toolchain.
- [x] Port and provenance-record the minimal PNTAnd import closure.
- [x] Expose Chebyshev-psi and prime-counting PNT interfaces.
- [x] Transfer the effective psi estimate to theta, with its explicit
  square-root prime-power correction and an `O(x / log x)` partial-summation
  facade.
- [x] Provide a natural-number facade used by Chen.
- [x] Add elementary finite prime sums, products, positivity, monotonicity, and
  logarithmic-factor estimates.
- [x] Enforce zero executable `sorry`/`admit`, full builds, and an axiom audit
  in CI.

### v0.2 — reusable Mertens layer

The two independent work lines below may proceed in parallel after agreeing on
the common asymptotic/error-term API.

- [x] Establish the finite Abel-summation bridge from reciprocal-prime sums
  to Chebyshev theta.
- [x] Separate the exact `log log x` main term and the endpoint error of that
  bridge.
- [x] Add the generic improper-integral tail estimate for the
  `1 / (x log² x)` kernel.
- [x] Prove local integrability and integrable asymptotic domination of the
  Chebyshev-theta error kernel.
- [x] Define the generic Mertens-II constant and identify finite error
  integrals with their improper tails.
- [x] Derive the exact Mertens-II error decomposition and the error-kernel
  tail rate.
- [x] **Mertens II:** prove the reciprocal-prime sum estimate from the PNT
  facade plus partial/Abel summation, including a natural-number API.
- [x] **Canonical Mertens product:** build the convergent quadratic correction
  and derive the `O(1 / log² x)` Euler-product estimate from Mertens II.
- [x] Add the finite logarithmic product bridge; the limiting correction and
  its Euler--Mascheroni constant identification remain separate milestones.
- [x] Define the zero-extended logarithmic correction and prove its absolute
  convergence to the canonical correction constant.
- [x] Bound the correction tail by `2 / x` using the integral test.
- [x] Derive the Mertens product logarithm with its canonical constant and
  `O(1 / log x)` error; identifying that constant with Euler's constant is
  still a separate Abelian bridge.
- [x] Establish the normalized zeta--von Mangoldt bridge at `s = 1`.
- [x] Specialize the Euler-log expansion to real parameters and split it into
  the prime Dirichlet term plus the convergent correction.
- [x] Prove the scaled logarithmic Gamma kernel giving `-γ`.
- [x] Prove the Abel/Mellin representation of the prime Dirichlet sum for
  every positive displacement `ε > 0`.
- [x] Perform the logarithmic change of variables to the exponential Abel
  kernel and prove a generic `O(1/u)` remainder-vanishing theorem.
- [x] Prove that the prime finite-part limit implies the required constant
  identity via the normalized zeta limit.
- [x] Prove the Abelian finite-part limit and conclude
  `mertensSecondConstant + logarithmicCorrectionLimit = γ`.
- [ ] Add namespace-level compatibility lemmas relating the generic finite
  objects to downstream definitions.

### v0.3 — downstream migration

- [x] Replace Chen's local PNT placeholder with the public natural-number PNT.
- [x] Replace Chen's Mertens-II placeholder with the generic theorem.
- [x] Replace Chen's product-formula placeholder with the generic theorem.
- [ ] Keep sieve notation and Chen-specific consequences in
  `chen-theorem-lean`; move only mathematically reusable results here.

### v0.4 — reusable sieve layer

- [x] Migrate the generic sieve layer (Goldbach density, Selberg identities,
  distribution, singular series, linear sieve, Bombieri--Vinogradov
  interfaces) from Chen into `AnalyticNumberTheory/Sieve/`.
- [x] Correct the lower sieve function on `(3, 5]` to the standard Buchstab
  value `f(s) = 2e^γ·log((s-1)/2)/s`.
- [x] **Legacy JR algebra record (#5):** formalize
  `UniformJurkatRichertLowerBound` (constants precede `∀ N`) and the finite
  seam `siftedSum_lower_bound_of_mainTerm`. These declarations preserve useful
  finite algebra, but use the refuted `D/z` parameter and all-divisor error,
  so they are not source-valid Chen inputs.
- [ ] **Compact-support repair (#66):** revise the lower-sieve consumer so a
  supported lower Möbius sequence keeps `errSum(μ⁻)` (hence only `d ≤ D`)
  instead of being widened to all-divisor `errSum(1)`; the written
  specification and source-audit gates are in
  `COMPACT_SUPPORT_LOWER_SIEVE_AUDIT.md`.
- [ ] **Correct linear-sieve ratio:** migrate the JR function argument from
  the false scale `D/z` to `log D/log z`, then prove the Chen rounded scales
  lie in the source-valid interval before applying the lower sieve; see
  `SIEVE_RATIO_PARAMETER_AUDIT.md`.
- [ ] **Genuine Li normalization:** replace the working `x/log x` sieve main
  term before asking for arbitrary-log-saving distribution estimates; the
  exact modulus-one obstruction and migration order are recorded in
  `SIEVE_MAIN_TERM_NORMALIZATION_AUDIT.md`.
- [ ] **Quantitative `pi-Li` facade:** promote the genuine interval integral
  already used by PNTAnd and formalize the medium-PNT-to-`pi-Li` transfer for
  the modulus-one Chen term; the written derivation is in
  `PNT_TO_PI_LI_WRITTEN_PROOF.md`.
- [ ] **Chen `a = 1` weighted BV seam:** after the Li migration, expose the
  source-matched weighted statement at the delta weight `f = 1_{a=1}` and
  transport it only to compactly supported lower-sieve moduli. This is not the
  current generic Pan principal-part chain; see `A1_WEIGHTED_BV_SOURCE_MATCH.md`.
- [x] **Selberg upper-bound sieve (#6):** add
  `AnalyticNumberTheory/Sieve/SelbergUpperBound.lean` with the generic
  Selberg weights, the Mathlib Λ²-sieve bridges, and the optimal-weight
  theorem `selberg_upper_bound_optimal`
  (`siftedSum ≤ totalMass · (Σ selbergTerms)⁻¹ + errSum(Λ²w*)`), plus the
  uniform target `UniformSelbergUpperBound`.
- [ ] Prove the uniform supported main-term estimate
  `UniformSupportedJurkatRichertMainTerm`
  (`mainSum(μ⁻) ≥ V(z)·(f(log D/log z) - η)`), the analytic core of issue #5.
- [ ] Plug the Mertens/singular-series main-term estimate and the weighted
  Pan error into the Selberg upper bound for the Chen constant
  `3.9404·𝔖(N)·N/log²N` (issue #6 acceptance).
- [x] **Weighted Pan--BV input (#7):** formalize the uniform weighted
  distribution input `WeightedPanCondition`, the `3^{ω(d)}` lcm-pair weight
  origin (`lcmPairCount` / `lcmPairWeightedSum`), the generic `errSum` seam,
  and the precise classical target `PanMeanValueUniform`.
- [x] **Truncated singular series uniform lower bound (chen #3):**
  `singularSeriesTruncated_ge_half` — `𝔖(N,z) ≥ 1/2` for every `N` and
  `z ≥ 2`, the twin-prime-constant-level input for the Chen main-term lower
  bound (finite-product/telescope argument, no Mertens needed).
- [x] **Selberg upper bound in sieve-product form:** the optimal Λ² bound
  re-expressed as `siftedSum ≤ totalMass·V(z) + errSum` via
  `selbergMainTerm_eq_prod_one_sub_nu` /
  `selbergMainTerm_eq_sieveProduct` / `selberg_upper_bound_sieveProduct`,
  the exact main-term shape consumed by the Chen Ω upper bound (chen #7).
- [x] **Selberg Λ² error-term bridge:** for unit-bounded weights,
  `errSum(Λ²w) ≤ Σ_{d | P} 3^{ω(d)}·|rem d|`
  (`errSum_lambdaSquared_le_threeOmegaWeightedPanRemainder`), the exact
  classical Selberg error form feeding the Pan input into the Ω upper bound.
- [x] **Optimal Selberg weight = Möbius:** the X-equation
  `Σ_{d ⊇ l} ν(d)·μ(d) = g(l)·μ(l)·T`, hence `mainSum(Λ²μ) = (Σg)⁻¹`
  (`mainSum_lambdaSquared_moebius_eq`) and the full classical Selberg bound
  `siftedSum ≤ totalMass·V + Σ 3^{ω(d)}·|rem d|`
  (`selberg_upper_bound_moebius_pan`), with the unit-bounded weight `μ`.
- [ ] Prove `PanMeanValueUniform` (large sieve / Vaughan identity), the
  analytic core of issue #7, and close the bridge from it to
  `WeightedPanCondition` with PNT-level main-term estimates.

## Boundary rule

A declaration belongs here when its statement is useful without importing a
particular sieve or target theorem. Definitions tied to Chen's singular series,
sieve weights, or final theorem remain in the Chen repository.
