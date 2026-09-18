# Linear-sieve parameter audit: `log D / log z`, not `D / z`

## Finding

The current ANT Jurkat--Richert interfaces feed the sieve function with

```text
DN(N) / zN(N).
```

This is not the classical linear-sieve parameter. The source parameter is

```text
s(N) = log(DN(N)) / log(zN(N)),                                (S)
```

where `D` is the level and `z` is the sieving limit. This is an interface
error, not a missing constant or an unproved asymptotic estimate.

Accordingly, the current appearances of

```text
fs (DN N / zN N)
```

in `UniformJurkatRichertMainTerm`, `UniformJurkatRichertLowerBound`, and
their finite transport theorem are not source-faithful JR targets.

## 1. Exact Chen scale check

The intended Chen scales are, up to floors and logarithmic factors,

```text
z(N) = N^(1/10),
D(N) = N^(1/2) / log^B N.
```

The classical parameter is therefore

```text
log D(N) / log z(N)
 = (1/2 log N - B log log N) / (1/10 log N)
 = 5 - 10B log log N / log N
 -> 5.                                                        (1)
```

This is why the explicit linear-sieve formula on the interval `(3,5]` is
relevant to the Chen lower bound.

By contrast, the currently encoded quotient is

```text
D(N)/z(N) = N^(2/5)/log^B N -> infinity.                      (2)
```

It is not approximately five. It eventually lies above five for every fixed
`B`, and hence selects the `s > 5` branch of the current `sieveFunctionf`.
That branch is explicitly documented in `LinearSieve.lean` as a placeholder,
not as the delayed Buchstab/Jurkat--Richert recursion.

Thus no Chen constant, positivity assertion, or source match may consume the
present `fs (D/z)` interface.

## 2. Correct replacement interface

The first repair is semantic and should precede coefficient construction:

```text
sieveRatio(D,z) = log D / log z,
```

defined only under explicit positivity and non-unit hypotheses such as
`1 < z` and `0 < D`. A robust uniform JR main-term specification has the
shape

```text
exists N0 eta0>0, for every even N >= N0,
  exists muMinus_N,
    IsLowerMoebius(muMinus_N)
    and |muMinus_N(d)| <= 1
    and support_D(muMinus_N)
    and
      V_N * (f(log(D_N)/log(z_N) - eta0)
        <= mainSum(muMinus_N).                                (JR)
```

The placement of the loss term depends on the chosen source convention
(`f(s)-eta`, `f(s)(1-eta)`, or an explicit `o(1)`); the chosen form must be
copied from the source used for the formalization. What is non-negotiable is
the logarithmic ratio in the argument of `f`.

For the Chen application, the next written lemma should bound the rounded
ratio in a compact interval inside `(3,5]` for sufficiently large `N`, or use
the source's one-sided version if its level is chosen slightly differently.
Only then is the explicit `(3,5]` formula for `sieveFunctionf` relevant.

## 3. Relationship to the other repairs

This is independent of, and cumulative with, the previously identified
interface repairs:

```text
wrong sieve parameter D/z       -> use log D/log z,
all-divisor lower-sieve error   -> retain coefficient support d <= D,
x/log x distribution main term -> use genuine Li,
unsigned lcm expansion          -> finish signed MainB cancellation first.
```

Fixing only one of these leaves a different invalid consumer seam. In
particular, compact support makes the distribution range meaningful, while
the logarithmic ratio makes the JR main term meaningful.

## 4. Formalization gate

Before implementing a supported JR interface, require all of the following:

1. an explicit `sieveRatio(D,z)` definition with its domain hypotheses;
2. a theorem identifying the Chen rounded level and sieving limit with a
   source-valid range for that ratio;
3. no use of the placeholder `s > 5` branch in a Chen lower-main-term claim;
4. compact coefficient support expressed at the same level `D`; and
5. a source statement whose error convention and quantifier order match (JR).

The falsifier is elementary: substituting `D=N^(1/2)/log^B N` and
`z=N^(1/10)` into a proposed Chen JR interface must yield a parameter tending
to five. If it tends to infinity, the interface has used `D/z` and is wrong.
