import math
from math import log

def mobius_sieve(n):
    mu = [1]*(n+1)
    for i in range(2, n+1):
        for j in range(i, n+1, i):
            mu[j] *= -1
        ii = i*i
        for j in range(ii, n+1, ii):
            mu[j] = 0
    return mu

def omega(n):
    cnt = 0
    d = 2
    while d*d <= n:
        if n % d == 0:
            cnt += 1
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        cnt += 1
    return cnt

def phi(n):
    r = n; m = n; d = 2
    while d*d <= m:
        if m % d == 0:
            r -= r//d
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        r -= r//m
    return r

for Q in [20, 40, 80, 160, 320]:
    m = Q*Q
    mu = mobius_sieve(Q)
    L = [0.0]*(m+1)
    for n in range(1, m+1):
        L[n] = log(n)
    S = sum(L[n]**2 for n in range(1, m+1))
    lhs = 0.0
    for q in range(1, Q+1):
        if mu[q] == 0:
            continue
        w = 3**omega(q)
        phiq = phi(q)
        inner = 0.0
        for a in range(1, q):
            if math.gcd(a, q) != 1:
                continue
            s = 0.0
            n = a
            while n <= m:
                s += L[n]
                n += q
            inner += s*s
        lhs += w * phiq * inner
    rhs = (m + Q*Q) * S
    print(f"Q={Q} m={m}: LHS={lhs:.4e} RHS={rhs:.4e} ratio={lhs/rhs:.6f}")
