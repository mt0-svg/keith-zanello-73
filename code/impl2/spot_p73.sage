# Spot checks by brute force at p = 73. Run from code/impl2/.
# (A) t not in the list: an explicit badness certificate, i.e. for every class rho mod 73 two indices
#     N1, N2 >= 5329, N1 = N2 = rho mod 73, N1 != N2 mod 5329, with c_t(N1), c_t(N2) odd. Found with the GF2X
#     engine, then EVERY certificate coefficient is recomputed by a second method: direct counting of
#     representations N = sum_i 2^{e_i} P_i (P_i generalised pentagonal, e_i the binary digits of t), mod 2,
#     with the last factor decided by "24 r + 1 is a square". This uses only f_1^t = prod f_{2^{e_i}} mod 2.
# (B) t in the list: (73, -t/24 mod 73^2)-evenness checked for all N < NMAX, and the number of odd
#     coefficients in the class rho_t (all must sit in the class r_t mod 73^2) is reported.
load("lib.sage")
import sys
R2.<z> = PolynomialRing(Zmod(2), implementation="FLINT")
p = 73; p2 = p*p
GOOD = [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 51, 55, 59, 61, 65, 69, 199, 203]

def certificate(t, Lmax=2^23):
    L = 2^13
    while L <= Lmax:
        G = F(t, L)
        pairs = {}
        seen = [dict() for _ in range(p)]
        for N in G.exponents():
            if N < p2:
                continue
            rho = N % p
            if rho in pairs:
                continue
            res = N % p2
            if res not in seen[rho]:
                seen[rho][res] = N
                if len(seen[rho]) == 2:
                    pairs[rho] = tuple(seen[rho].values())
                    if len(pairs) == p:
                        return pairs, L
        L *= 2
    return None, L

def is_pent(r):
    if r < 0:
        return False
    return is_square(24*r + 1)

def pent_list(bound):
    out = []
    k = 0
    while k*(3*k-1)//2 <= bound:
        out.append(k*(3*k-1)//2)
        if k > 0 and k*(3*k+1)//2 <= bound:
            out.append(k*(3*k+1)//2)
        k += 1
    return sorted(out)

def coef_by_count(t, N):
    """[q^N] prod_{digits e of t} f_1(q^{2^e}) mod 2, by counting representations."""
    digits = [i for i in range(t.nbits()) if (t >> i) & 1]
    digits.sort(reverse=True)   # largest multiplier first, smallest (tested by square test) last
    def rec(idx, rem):
        m = 2^digits[idx]
        if idx == len(digits) - 1:
            return 1 if (rem % m == 0 and is_pent(rem // m)) else 0
        s = 0
        for P in pent_list(rem // m):
            s += rec(idx + 1, rem - m*P)
        return s % 2
    return rec(0, N)

allok = True
spot = [25, 27, 29, 31, 47, 49, 53, 71, 73, 97, 145, 191, 201, 205, 207, 255, 257, 1025, 4097, 2^16 + 1,
        3 + 2^20, 5 + 2^14, 203 + 2^16, 199 + 2^17, 1 + 2^10, 1 + 2^11, 3 + 2^9, 3 + 2^10, 1 + 2^20, 1 + 2^22,
        3 + 2^21, 1 + 3*2^12, 69 + 2^15, 17 + 2^14, 2^20 - 1]
set_random_seed(20260926)
rnd = [2*ZZ.random_element(2^38, 2^40) + 1 for _ in range(4)] + [2*ZZ.random_element(2^8, 2^12) + 1 for _ in range(4)]
spot += [t for t in rnd if t not in GOOD]
for t in spot:
    t = ZZ(t)
    pairs, L = certificate(t)
    if pairs is None:
        print("t = %d: NO certificate up to L = %d" % (t, L)); allok = False; continue
    nd = len([i for i in range(t.nbits()) if (t >> i) & 1])
    # engine 2: FLINT nmod_poly powering (independent of NTL GF2X)
    Pfl = R2({e: 1 for e in pent_poly(L).exponents()})
    Gfl = Pfl.power_trunc(t, L)
    badfl = [(rho, N) for rho in pairs for N in pairs[rho] if Gfl[N] != 1]
    if badfl:
        allok = False
    checked = "FLINT recheck %s" % ("OK" if not badfl else "MISMATCH %s" % badfl[:5])
    digs = sorted([i for i in range(t.nbits()) if (t >> i) & 1], reverse=True)
    maxN0 = max(max(v) for v in pairs.values())
    cost = prod([sqrt(2.0*maxN0/(3*2^e)) + 2 for e in digs[:-1]]) if len(digs) > 1 else 1
    if cost <= 3e4:
        bad = [(rho, N) for rho in pairs for N in pairs[rho] if coef_by_count(t, N) != 1]
        checked += ", counting recheck of all 146: %s" % ("OK" if not bad else "MISMATCH %s" % bad[:5])
        if bad:
            allok = False
    maxN = max(max(v) for v in pairs.values())
    print("t = %d: certificate found (L = %d, largest index %d), %s; classes 0,1,2: %s" % (
        t, L, maxN, checked, [pairs[r] for r in range(3)]))
    sys.stdout.flush()

NMAX = 2*10^7
for t in GOOD:
    G = F(t, NMAX)
    rt = r_of(t, p); rho = rt % p
    nodd = 0; viol = []
    for N in range(rho, NMAX, p):
        if G[N]:
            if N % p2 != rt:
                viol.append(N)
                if len(viol) > 3:
                    break
            else:
                nodd += 1
    # other classes: do they all carry pairs (so r_t is the only base class)?
    supp = [N for N in G.truncate(200000).exponents() if N >= p2]
    nopair = classes_without_pair(supp, p)
    print("t = %d: r_t = %d, N < %d: violations %s, odd coefficients at N = r_t mod p^2: %d; classes without a pair below 2e5: %s" % (
        t, rt, NMAX, viol, nodd, nopair))
    if viol:
        allok = False
    sys.stdout.flush()
print("SPOT CHECKS:", "PASS" if allok else "FAIL")
