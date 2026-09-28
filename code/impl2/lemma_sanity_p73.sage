# Numerical sanity checks of the lemma statements and of the definition. Run from code/impl2/.
# (A) Literal definition: for sample t, test every base r in [0, 5329) directly on c_t(5329 n + 73 k + r),
#     n >= 0, 1 <= k <= 72, N < NMAX; list the bases that survive. Bad t: none; listed t: exactly r_t.
# (B) Lemma 14 conclusion: for T = 1 + 2^K w (resp. 3 + 2^K w) with K >= K0 and w odd,
#     [q^{2^K M + s}] F_T = c_w(M) for all 0 <= M <= 300 and all small s (|k| <= 146, resp. 0 <= k <= 146).
# (C) the identity behind Lemma 13: for T = t + 2^K u (u odd, t < 2^K), F_T = F_t (1 + x^{2^K}) mod x^{2^{K+1}}.
load("lib.sage")
import sys
p = 73; p2 = p*p
GOOD = [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 51, 55, 59, 61, 65, 69, 199, 203]
ok = True

def surviving_bases(t, NMAX):
    G = F(t, NMAX)
    odd = [[] for _ in range(p)]
    for N in G.exponents():
        odd[N % p].append(N)
    surv = []
    for r in range(p2):
        killed = False
        for N in odd[r % p]:
            # literal: N = p^2 n + k p + r with n >= 0, 1 <= k <= p-1
            d = N - r
            if d < 0:
                continue
            m = d // p            # d is divisible by p since N = r mod p
            k = m % p; n = m // p
            if 1 <= k <= p - 1 and n >= 0:
                assert p2*n + k*p + r == N
                killed = True
                break
        if not killed:
            surv.append(r)
    return surv

NMAX = 400000
for t in [1, 3, 5, 7, 23, 51, 69, 199, 203, 25, 27, 71, 205, 257, 1025, 4097]:
    s = surviving_bases(t, NMAX)
    exp = [r_of(t, p)] if t in GOOD else []
    print("(A) t = %d: bases surviving on N < %d: %s (expected %s)" % (t, NMAX, s, exp))
    if s != exp:
        ok = False
    sys.stdout.flush()

# (B)
kap, mu = 146, 300
pent_small = sorted(set(k*(3*k-1)//2 for k in range(-kap, kap+1)))
tri_small = [k*(k+1)//2 for k in range(0, kap+1)]
set_random_seed(7)
for (tau, small, Ks) in [(1, pent_small, [10, 11, 13]), (3, tri_small, [9, 10, 12])]:
    for K in Ks:
        for w in [1, 3, 5, 255, 511, 513, 2*ZZ.random_element(2^20) + 1]:
            T = tau + 2^K * w
            L = 2^K * mu + max(small) + 1
            GT = F(T, L)
            Gw = F(w, mu + 1)
            bad = 0
            for M in range(mu + 1):
                cw = Gw[M]
                for s in small:
                    if GT[2^K*M + s] != cw:
                        bad += 1
            if bad:
                ok = False
            print("(B) tau = %d, K = %d, w = %d: special-index mismatches %d" % (tau, K, w, bad))
            sys.stdout.flush()

# (C)
for (t, K) in [(5, 13), (69, 14), (199, 16), (203, 16), (203, 18)]:
    for u in [1, 3, 7, 12345]:
        T = t + 2^K * u
        L = 2^(K+1)
        lhs = F(T, L)
        rhs = (F(t, L) * (1 + x^(2^K))).truncate(L)
        print("(C) t = %d, K = %d, u = %d: identity %s" % (t, K, u, lhs == rhs))
        if lhs != rhs:
            ok = False
print("LEMMA SANITY:", "PASS" if ok else "FAIL")
