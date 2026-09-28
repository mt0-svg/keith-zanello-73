# Brute force over all odd t < 2^B at p = 73, with no lemma at all. Run from code/impl2/.
# For each odd t, search a badness certificate (a pair in every class mod 73 among the odd coefficients of
# f_1^t at indices N >= 5329) in f_1^t mod (2, x^L), L = 2^13, 2^14, ..., 2^LMAXEXP (GF2X engine).
# Expected: a certificate for every t outside the list; none for the 20 listed values (they are good).
load("lib.sage")
import sys
p = 73; p2 = p*p
GOOD = set([1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 51, 55, 59, 61, 65, 69, 199, 203])
B = int(sys.argv[1]) if len(sys.argv) > 1 else 16
LMAXEXP = max(B + 1, 17)

def has_certificate(t):
    L = 2^13
    while L <= 2^LMAXEXP:
        G = F(t, L)
        seen = [set() for _ in range(p)]
        done = 0
        for N in G.exponents():
            if N < p2:
                continue
            s = seen[N % p]
            if len(s) < 2:
                s.add(N % p2)
                if len(s) == 2:
                    done += 1
                    if done == p:
                        return L
        L *= 2
    return 0

nocert = []
hist = {}
for t in range(1, 2^B, 2):
    L = has_certificate(t)
    if L == 0:
        nocert.append(t)
    else:
        hist[L] = hist.get(L, 0) + 1
print("odd t < 2^%d: certificate length histogram %s" % (B, sorted(hist.items())))
print("t without certificate up to L = 2^%d (%d values): %s" % (LMAXEXP, len(nocert), nocert[:100]))
print("ALL-T CHECK:", "PASS" if set(nocert) == GOOD else "FAIL (differs from the list)")
