# From ANT's medium PNT to the required `pi - Li` bound

## Status

This is a written proof of the modulus-one analytic supply required by the
compact Chen lower-sieve specification. It identifies the exact existing ANT
results needed for a future Lean proof; it is not itself a new Lean theorem.

The target is: for every fixed `A > 0`, there are `C_A, X_A > 0` such that
for real `x >= X_A`,

```text
|pi(x) - Li(x)| <= C_A x/log^A x,                             (PNT-Li)
Li(x) = integral from 2 to x of dt/log t.
```

For Chen, take the natural argument `x = N-2`. This controls the supported
lower-sieve term at `d=1`; it is deliberately separate from the AP mean-value
theorem used for `d >= 2`.

## 1. Existing kernel-checked inputs

The following are already present in the repository.

1. `PrimeDistribution.chebyshevPsi_medium_error` exports
   ```text
   psi(x)-x = O(x exp(-c (log x)^(1/10)))                     (1)
   ```
   for some `c>0`.
2. `PrimeDistribution.chebyshevTheta_medium_error` transfers this to
   ```text
   theta(x)-x = O(sqrt(x) + x exp(-c (log x)^(1/10))).         (2)
   ```
   It uses the standard kernel-checked prime-power difference
   `psi-theta = O(sqrt(x))`.
3. `PrimeNumberTheoremAnd/Consequences.lean`, `pi_asymp_aux`, gives the exact
   partial-summation identity
   ```text
   pi(x) = theta(x)/log x
           + integral_2^x theta(t)/(t log^2 t) dt,             (3)
   ```
   with `pi(x)` represented as `Nat.primeCounting floor(x)`.
4. `integral_log_inv` gives
   ```text
   Li(x) = x/log x - 2/log 2 + integral_2^x dt/log^2 t.        (4)
   ```

Item 4 is also the exact reason the working expression `x/log x` cannot be
used as an arbitrary-log-saving distribution main term.

## 2. Exact error identity

Put `E(t) = theta(t)-t`. Subtract (4) from (3). Since
`t/(t log^2 t) = 1/log^2 t`, the main integrals cancel, and for `x >= 2`

```text
pi(x) - Li(x)
  = E(x)/log x + integral_2^x E(t)/(t log^2 t) dt + 2/log 2.  (5)
```

The constant is an endpoint convention, not an error: this `Li` is zero at
`2`. For example at `x=2`, the right side equals one, as it must.

Thus it suffices to bound the endpoint term and the integral in (5).

## 3. Quantitative estimate

Write

```text
u(x) = exp(-c (log x)^(1/10)).
```

By (2), for large `t`,

```text
|E(t)| <= K (sqrt(t) + t u(t)).                               (6)
```

Choose `c' = c / 2^(1/10)`. The endpoint contribution is

```text
|E(x)|/log x
 <= K sqrt(x)/log x + K x u(x)/log x
 << x exp(-c' (log x)^(1/10))/log x.                          (7)
```

The last domination holds because `sqrt(x)` is smaller than
`x exp(-c' log(x)^(1/10))` eventually.

For the integral, split at `sqrt(x)` (with any fixed lower cutoff large
enough for (6)). The bounded initial interval is `O(1)`. On
`[T,sqrt(x)]`, the square-root part contributes

```text
integral_T^sqrt(x) dt/(sqrt(t) log^2 t) = O(x^(1/4)).          (8)
```

and the exponential part is at most `O(sqrt(x))` after discarding the
logarithmic denominator. Both are eventually bounded by the right side of
(7).

On `[sqrt(x),x]`, monotonicity gives

```text
u(t) <= u(sqrt(x)) = exp(-c' (log x)^(1/10)),
1/log^2 t <= 4/log^2 x.
```

Therefore the exponential piece is at most

```text
K integral_sqrt(x)^x u(t)/log^2 t dt
 <= 4K x exp(-c' (log x)^(1/10))/log^2 x,                     (9)
```

and the square-root piece is `O(sqrt(x)/log^2 x)`. Combining
(7)--(9) with the constant in (5) yields, for some `K',c'>0`,

```text
|pi(x)-Li(x)|
 <= K' x exp(-c' (log x)^(1/10))/log x                       (10)
```

for every sufficiently large `x`.

Finally, exponential decay beats every fixed log power:

```text
exp(-c' (log x)^(1/10)) <= log^(-(A-1)) x
```

eventually (trivially if `A <= 1`; otherwise use
`(log x)^(1/10) / log log x -> infinity`). Inserting this in (10) proves
`PNT-Li` for every fixed `A>0`.

## 4. Chen endpoint and consumer

For an even `N`, the unsifted prime support ends at `N-2`, so the matching
term is

```text
|Nat.primeCounting (N-2) - Li(N-2)| <<_A N/log^A N.           (11)
```

Replacing `N-2` by `N` only changes the displayed scale by harmless eventual
constants. This is the `d=1` term in the supported error sum. Its main term
must be exactly `Li(N-2)`: using `N/log N` instead recreates the refuted
deterministic order `N/log^2 N` discrepancy.

Together with `A1_WEIGHTED_BV_SOURCE_MATCH.md`, the error budget splits as

```text
d = 1                       : (PNT-Li),
2 <= d <= D and d | P_N     : weighted BV at a=1,
rem_N(d) - AP-error_N(d)    : signed MainB finite correction.
```

No term in this list needs the false all-divisor tail or an absolute value
inside the forbidden-divisor Möbius expansion.

## 5. Formalization plan and checks

The future formal proof should expose the following reusable lemmas in this
order:

1. `primeLogIntegral(x) = integral_2^x 1/log t dt`, with the endpoint
   convention from `Consequences.lean`;
2. the exact `pi_minus_primeLogIntegral` identity (5), derived from
   `pi_asymp_aux` and `integral_log_inv`;
3. a quantitative integral lemma implementing the split at `sqrt(x)`;
4. the exponential-versus-log-power eventual inequality; and
5. a natural-number corollary at `N-2`.

Acceptance criterion: the final theorem must have constants and threshold
outside the universal `x`, use genuine `Li`, and be independently printable
without importing Chen. A mere `pi(x) ~ x/log x` theorem is insufficient for
this consumer.
