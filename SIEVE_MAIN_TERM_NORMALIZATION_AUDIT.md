# Sieve main-term normalization: exact counterexample audit

## Decision

The current sieve symbol `logarithmicIntegral(x)` is defined as `x / log x`.
It is not the classical logarithmic integral.  Consequently any sieve or
Pan/BV interface that asks for an error `O_A(x/log^A x)` for every `A>0`
relative to this working main term is false already at modulus one.

This is an exact asymptotic obstruction, not a missing Lean lemma and not a
weakness of the available medium PNT.  A true arbitrary-log-saving
distribution statement must use the genuine integral main term

```text
Li(x) = integral from 2 to x of dt/log t
```

(with the chosen endpoint convention), or else carry the deterministic
secondary terms explicitly.

## 1. The current definition

In `AnalyticNumberTheory/Sieve/BombieriVinogradov.lean`, the definition is

```text
logarithmicIntegral(x) := x/log x.
```

`panDistributionError` and the Chen sieve remainder use this expression as
their main term.  The in-code comment correctly says it is a working
definition, but a working first asymptotic term cannot be substituted for
`Li` inside a beyond-all-logarithmic-orders error statement.

## 2. Paper proof of the obstruction

Write

```text
L(x) = integral_2^x dt/log t.
```

Integration by parts gives

```text
L(x) = x/log x - 2/log 2 + integral_2^x dt/log^2 t.            (1)
```

A second integration by parts, or the usual endpoint estimate, gives

```text
integral_2^x dt/log^2 t = x/log^2 x + O(x/log^3 x).            (2)
```

The medium PNT for Chebyshev's psi, after the standard theta transfer and
partial summation, yields the genuine estimate

```text
pi(x) = L(x) + O(x exp(-c (log x)^(1/10)) / log x)             (3)
```

for some `c>0`.  Its error is smaller than `x/log^A x` for every fixed `A`.
Combining (1)--(3) instead yields

```text
pi(x) - x/log x = x/log^2 x · (1 + o(1)).                     (4)
```

In particular, for sufficiently large `x`,

```text
|pi(x) - x/log x| ≥ x/(2 log^2 x).                             (5)
```

If this error were `≤ C x/log^A x` for every prescribed `A`, take `A=3`.
Equation (5) would force `log x ≤ 2C` for all large `x`, a contradiction.

Thus neither a modulus-one Pan error nor the Chen `d=1` remainder can have
arbitrary log saving under the current normalization.

## 3. Scope of the damage

The issue is not confined to `d=1`.  For a coprime residue class modulo `q`,
the standard main term is `Li(x)/phi(q)`, whereas replacing it by
`x/(phi(q) log x)` leaves a deterministic secondary contribution of size
roughly `x/(phi(q) log^2 x)`.  An averaged BV/Pan theorem cannot erase this
deterministic mismatch by cancellation after absolute values are taken.

Therefore the following current-style aspirations are not valid theorem
targets without a normalization repair:

- arbitrary-log-saving `panDistributionError` bounds defined with `x/log x`;
- `ChenWeightedPanInput` or truncation inputs that consume those errors at
  arbitrary exponent `A`;
- a d=1 "quantitative PNT facade" relative to `x/log x` with arbitrary
  logarithmic saving.

## 4. Correct replacement

Introduce a genuine sieve main-term function, for example

```text
primeLogIntegral(x) = integral from 2 to x of dt/log t,
```

with an explicit convention for small `x`.  Then define the distribution
error by

```text
pi(x;q,l) - primeLogIntegral(x)/phi(q).
```

The required interfaces must be rebuilt against this function:

1. the ANT `distributionError` / `panDistributionError` definitions;
2. the Pan/Vaughan main-term decomposition and its source statement;
3. the Chen sieve total mass and `rem` identity, using the matching endpoint
   (`Li(N-2)` where the prime support ends at `N-2`);
4. the compact-support lower-sieve transport from ANT #66;
5. the quantitative PNT facade at modulus one.

An alternative is to retain `x/log x` only for coarse main-term inequalities
and to state the error budget with the unavoidable `O(x/log^2 x)` deterministic
term.  That alternative cannot deliver the arbitrary-log-saving error needed
by the current Chen positivity route, so the genuine `Li` normalization is
the recommended architecture.

## 5. Relationship to the compact-support repair

Compact support and correct normalization solve different self-created
difficulties:

```text
all-divisor errSum(1)          -> preserve lower-coefficient support,
x/log x as exact distribution main term -> replace by genuine Li.
```

Both repairs are necessary before attaching a Pan/BV theorem.  Compact
support restricts the moduli; genuine `Li` removes the deterministic local
main-term error.  Neither replaces the remaining analytic work of proving the
specific weighted Pan/BV estimate.

## 6. Formalization gates

Before any claim that the corrected Chen chain is sorry-free, verify:

1. `primeLogIntegral` has a mathematically genuine definition and the chosen
   endpoint convention is used consistently.
2. The Medium PNT is transferred to an explicit `pi - Li` error at the
   strength actually consumed.
3. Every Pan/BV error and Chen remainder uses the same main term.
4. No remaining arbitrary-log-saving proposition is measured against merely
   `x/log x`.

The counterexample (5) is the stop condition: any proposed interface violating
it is false before formalization begins.
