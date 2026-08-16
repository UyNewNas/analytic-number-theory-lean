# Compact-support lower sieve: written interface audit

## Status

This is a written specification for ANT issue #66.  It identifies a
representation error in the current lower-sieve consumer and gives the
source-faithful replacement interface.  It is not a Lean implementation and
does not claim a new analytic theorem.

The target claim is a uniform lower-sieve inequality for a family of
`BoundingSieve`s.  Its category is mixed:

- the passage from supported coefficients to a supported finite error sum is
  finite algebra and should be kernel-checkable;
- the existence and main-term quality of the lower-sieve coefficients is the
  Jurkat--Richert/linear-sieve analytic-combinatorial supply;
- the estimate of the supported prime-distribution error is a Pan/BV supply,
  with the modulus-one term supplied separately by a quantitative PNT.

## 1. The current finite theorem and the loss of structure

For a `BoundingSieve S`, let

```text
E_S(μ) = Σ_{d | S.prodPrimes} |μ(d)| |S.rem(d)|.
```

This is exactly `S.errSum μ`.  ANT already proves the finite theorem

```text
S.totalMass · S.mainSum(μ⁻) - E_S(μ⁻) ≤ S.siftedSum,          (1)
```

whenever `μ⁻` is a lower Möbius sequence.  This is the correct algebraic
place at which a lower-sieve coefficient sequence enters.

The later theorem `siftedSum_lower_bound_of_mainTerm` replaces `E_S(μ⁻)` by

```text
E_S(1) = Σ_{d | S.prodPrimes} |S.rem(d)|.                      (2)
```

using only `|μ⁻(d)|≤1`.  The inequality is true but deliberately forgets
where `μ⁻` vanishes.  Calling (2) the finite counterpart of the classical
`Σ_{d≤D}|R_d|` is therefore invalid unless a support condition has separately
restricted the divisor sum.  This is a representation-created difficulty,
not evidence for a stronger prime-distribution theorem.

## 2. The supported error identity

Fix a natural cutoff `D`.  Define the supported remainder mass

```text
E_{S,D}(μ) = Σ_{d | S.prodPrimes, d≤D} |μ(d)| |S.rem(d)|.
```

Assume

```text
Support_D(μ) :  μ(d) ≠ 0 and d | S.prodPrimes  =>  d ≤ D.     (S)
```

Then finite termwise cancellation gives the exact identity

```text
E_S(μ) = E_{S,D}(μ).                                           (3)
```

No estimate is involved: every summand with `d>D` is zero.  With
`|μ(d)|≤1`, (3) yields

```text
E_S(μ) ≤ Σ_{d | S.prodPrimes, d≤D} |S.rem(d)|.                 (4)
```

The right side is the object that classical level-of-distribution hypotheses
actually address.  It must not be enlarged to all divisors merely to avoid
recording `(S)`.

## 3. Uniform compact lower-sieve specification

Let `SP N` be a family of bounding sieves with positive cutoffs `DN N`.  A
source-faithful replacement for the current uniform lower-bound interface is:

```text
UniformSupportedJurkatRichertLowerBound(SP,zN,DN,fs):

there exist N0 and eta0>0 such that for every even N≥N0
there exists μ⁻_N with
  (i)  IsLowerMoebius(μ⁻_N),
  (ii) |μ⁻_N(d)| ≤ 1 for every d,
  (iii) μ⁻_N(d) ≠ 0 and d | (SP N).prodPrimes
        implies d ≤ floor(DN N),
  (iv) sieveProductPrimeFactors(SP N)
       · (fs(DN N/zN N)-eta0) ≤ (SP N).mainSum(μ⁻_N),
and
  (SP N).totalMass · sieveProductPrimeFactors(SP N)
  · (fs(DN N/zN N)-eta0)
  - Σ_{d | (SP N).prodPrimes, d≤floor(DN N)}
      |(SP N).rem(d)|
  ≤ (SP N).siftedSum.                                         (5)
```

The proof of `(5)` is the finite chain `(1) -> (3) -> (4)` plus the main-term
inequality.  Its quantifier order is essential: `N0` and `eta0` precede the
universal quantifier over `N`; the coefficients may depend on `N`.

The difference from the old interface is not cosmetic.  The support clause
is what makes the phrase "level D" mathematically meaningful.

## 4. Chen transport map

For the corrected Chen sieve, write

```text
P(N) = correctedChenSiftingProduct(N),
D(N,B) = floor(sqrt(N)/(log N)^B),
Δ_N(d) = panDistributionError(N-2;1,d,N mod d).
```

The finite Chen bridge identifies its remainder at `d|P(N)` with the
corresponding prime-progression error up to the already-audited signed Möbius
correction.  Once the lower coefficients satisfy `(S)` with `D=D(N,B)`, the
only distributional sum to consume is of the form

```text
Σ_{d|P(N), 2≤d≤D(N,B)} |μ⁻_N(d)| |Δ_N(d)|.                    (6)
```

Since `|μ⁻_N(d)|≤1≤3^ω(d)`, it is bounded by the standard Chen a=1 weighted
Pan/BV sum on that same modulus range.  The restriction `d|P(N)` also gives
`gcd(N mod d,d)=1` for `d≥2`, so these are legitimate coprime residue classes
for the Pan maximum.  The exceptional `d=1` term is

```text
|π(N-2)-li(N-2)|,
```

and must be supplied by a quantitative PNT consequence, not by a BV theorem.

Crucially, no forbidden-divisor expansion occurs in (6).  The signed finite
Möbius cancellation is completed before the distribution estimate is invoked;
there is no individual `lcm(d,e)` error under an absolute value.

## 5. Relationship to the refuted all-divisor route

The current Chen truncation construction attempts to split the broad
`errSum(1)` into a Pan-covered range and a tail, then introduced a false
absolute-value `lcm(d,e)` input.  The exact `d=1,e=2` counterexample rules out
that input.  A tail-only statement for the remaining single-modulus errors is
logically sufficient for the old broad representation, but it is not the
preferred source match.

The compact-support interface removes the artificial all-divisor tail at its
origin.  It does not solve the analytic Pan/BV theorem; it places that theorem
on precisely the moduli which its level-of-distribution statement controls.

## 6. Audit gates before formalization

A Lean implementation may begin only after all of the following are stated
with exact definitions rather than prose:

1. A supported lower-Möbius coefficient family and the exact cutoff used in
   its support condition.
2. A kernel proof of `(3)` and the supported version of the lower-sieve
   inequality.
3. A main-term theorem satisfying clause (iv), with its uniform quantifiers.
4. A Chen bridge from the supported error sum to the a=1 weighted Pan/BV
   statement, including the separate `d=1` PNT lemma.
5. A source-level theorem whose weights, moduli, residue-class coprimality,
   and logarithmic saving match (6).

Failure conditions are equally clear: any proposed route that reverts to
`errSum(1)`, treats a non-coprime residue class as a Pan/BV class, or takes
absolute values before the signed forbidden-divisor cancellation has not met
this specification.

## 7. Literature orientation

The support principle is the standard linear-sieve architecture: the
Jurkat--Richert lower bound is expressed with a remainder sum at level `D`,
not all divisors of the sifting product.  For the closely related correction
to a Pan-et-al. simplification, see Zihao Liu, *A Corrected Simplified Proof
of Chen's Theorem* (2022), Section IV: exceptional non-coprime terms are
split from the coprime mean-value estimate rather than hidden inside it.

This reference is methodological orientation, not a proof of clauses (iii),
(iv), or the specific Chen Pan/BV supply above.  Those require a line-by-line
source match before any theorem claim.

Source: [arXiv:2203.07871](https://arxiv.org/abs/2203.07871).
