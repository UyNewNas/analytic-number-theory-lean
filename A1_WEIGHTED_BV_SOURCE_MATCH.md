# Chen `a = 1` weighted BV supply: source match

## Status and decision

This is a written source match for the analytic supply consumed by the
**compactly supported** Chen lower sieve. It is not a Lean implementation,
and it does not claim that the cited theorem has been formalized.

The decisive simplification is that this consumer has the delta weight

```text
f(a) = 1 if a = 1, and 0 otherwise.
```

It must therefore not be routed through ANT's generic Pan main-term chain.
That chain tries to control a principal `Li` sum for arbitrary bounded `f`;
its absolute-value formulation is genuinely too large. In the Chen `a = 1`
consumer the inner sum has one term, so there is no such main-term block.
The remaining supply is precisely a weighted Bombieri--Vinogradov statement.

This removes a representation-created obstruction. It does **not** prove the
remaining analytic theorem, nor does it repair a false statement by renaming it.

## 1. Source theorem

Liu, *A Corrected Simplified Proof of Chen's Theorem* (2022), Theorem 2,
states the following Pan--Wang--Ding mean-value input. For every fixed
`A > 0` there is `B = B(A)` such that, for all sufficiently large `x`,

```text
sum_{q <= x^(1/2) log^(-B) x}
  mu(q)^2 3^omega(q)
  max_{y <= x} max_{(l,q)=1}
    | sum_{(a,q)=1} f(a) Delta(y; a,q,l) |
  <<_A x/log^A x,                                             (P)

Delta(y; a,q,l) = pi(y; a,q,l) - Li(y/a)/phi(q).
```

Here `Li` is the genuine logarithmic integral, not the first asymptotic term
`x/log x`. The paper also explains why its use of `(a,q)=1` is essential:
the non-coprime part must be split off in the general switching application.

Source location: Theorem 2 is on pages 1--2; the correction is in Section IV
(pages 4--5), especially the separation of `R_1` after equation (13).

Source: [arXiv:2203.07871](https://arxiv.org/abs/2203.07871), Theorem 2 and
Section IV.

## 2. Exact `a = 1` specialization

Put `f = delta_1`. Since `1` is coprime to every `q`, the inner sum in (P)
is exactly

```text
Delta(y; 1,q,l) = pi(y; q,l) - Li(y)/phi(q).                  (A1)
```

Thus (P) specializes, with no `R_1` remainder, to

```text
sum_{q <= x^(1/2) log^(-B) x}
  mu(q)^2 3^omega(q)
  max_{y <= x} max_{(l,q)=1}
    |pi(y;q,l) - Li(y)/phi(q)|
  <<_A x/log^A x.                                             (WBV)
```

This is the correct reusable ANT-facing theorem specification. It has four
features that must remain visible in any later Lean interface:

| feature | required form | reason |
| --- | --- | --- |
| main term | genuine `Li(y)/phi(q)` | `y/log y` leaves a deterministic `y/log^2 y` error |
| moduli | `q <= sqrt(x)/log^B x` | exactly the level supplied by the source |
| weight | `mu(q)^2 3^omega(q)` | arises from the Selberg lcm-pair count |
| uniformity | `max_y max_(l,q)=1`, arbitrary fixed `A` | permits the Chen endpoint/residue specialization |

`WBV` is a **supply theorem**, not a consequence of ANT's present
fixed-parameter `bombieri_vinogradov` placeholder. The latter has the wrong
quantifiers and cannot be used as a substitute.

## 3. Transport to the supported Chen error

Let

```text
P_N = correctedChenSiftingProduct(N),
D_B(N) = floor(sqrt(N)/log^B N),
E_N(d) = pi(N-2; d, N mod d) - Li(N-2)/phi(d).
```

The proposed compact lower-sieve coefficients satisfy

```text
muMinus_N(d) != 0 and d | P_N  =>  d <= D_B(N).               (S)
```

For `d | P_N`, the repository's finite arithmetic already records the two
facts required by the source specialization:

```text
d is squarefree,                 so mu(d)^2 = 1;
gcd(N mod d,d) = 1 for d >= 2.                                 (C)
```

The `d` in the supported sum are a subset of the `q` in `WBV`, evaluated at
`x=N`, `y=N-2`, and `l=N mod d`. Positivity of the summands and (C) therefore
give the paper implication

```text
sum_{d | P_N, 2 <= d <= D_B(N)}
  3^omega(d) |E_N(d)| <<_A N/log^A N.                          (T)
```

Since `|muMinus_N(d)| <= 1 <= 3^omega(d)`, (T) also controls the non-unit
coefficient error that actually occurs in the lower-sieve inequality.

This is the precise point at which the compact-support repair is consumed:
without (S), the summation contains divisors larger than the source level and
the implication from `WBV` is invalid.

## 4. The three supplies that do not disappear

The source match closes neither the whole Chen theorem nor the old all-divisor
error interface. The following obligations remain separate and must not be
silently folded into `WBV`:

1. **Modulus one.** The term `d=1` is absent from the coprime-residue maximum
   in the useful form above. It requires the quantitative PNT consequence
   ```text
   |pi(N-2) - Li(N-2)| <<_A N/log^A N.
   ```
   ANT's medium PNT is the intended source, after a written partial-summation
   transfer and then formalization.
2. **Signed forbidden-divisor correction.** After both sides use the same
   `Li(N-2)` endpoint,
   ```text
   rem_N(d) - E_N(d)
     = sum_{1 != e | F_N} mu(e) base_N(lcm(d,e)).
   ```
   The prior MainB audit controls its weighted supported sum. It is a finite
   signed cancellation followed by an elementary divisor estimate, not a
   Pan/BV statement.
3. **Lower-sieve coefficients and main term.** A Jurkat--Richert/linear-sieve
   theorem must actually produce coefficients satisfying (S) and the required
   positive main-term lower bound. This is ANT issue #66's other half.

Consequently the corrected consumer dependency is

```text
Medium PNT -> d=1 pi-Li bound
Pan Theorem 2 -> (WBV) -> supported d>=2 AP error
signed MainB -> rem minus AP error
compact Jurkat--Richert coefficients -> support (S) and main term
                 \             |             /
                  \------------v------------/
                       valid Chen lower-sieve error budget.
```

Every arrow above is labelled by a theorem type; none means that a current
`sorry`, a fixed-parameter existential constant, or the refuted absolute-value
`lcm(d,e)` sum is being accepted as analytic evidence.

## 5. Formalization gate

Do not formalize the old generic `PanMeanValueUniform -> WeightedPanCondition`
bridge for this consumer. Its generic principal-part bound has the wrong
shape and is not needed for `f = delta_1`.

The first formal interfaces should instead be:

1. a genuine `primeLogIntegral` and a modulus-one `pi-Li` theorem;
2. a `WeightedBVAtOne` proposition matching `WBV` exactly;
3. the finite subset transport from `WeightedBVAtOne` to (T);
4. the supported lower-sieve error identity; and
5. the already-audited signed MainB transport.

The stop conditions are exact: reject any proposed theorem that uses
`x/log x` as an arbitrary-log-saving error main term, drops the modulus range,
or reintroduces all divisors after the lower coefficient support has been
established.
