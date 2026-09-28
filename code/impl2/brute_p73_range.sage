# Extension of brute_p73.sage (brute force, no lemma) to odd t in [LO, HI) at p = 73. Run from code/impl2/ as
#   sage brute_p73_range.sage LO HI LMAXEXP
# For each odd t, search a badness certificate (a pair in every class mod 73 among the odd coefficients of
# f_1^t at indices N >= 5329, distinct mod 5329) in f_1^t mod (2, x^L), L = 2^13, ..., 2^LMAXEXP (GF2X engine).
# Prints the t without certificate; those are then treated by direct counting (r8 style) if they are of the
# sparse form tau + 2^K w.
load("lib.sage")
import sys
p = 73; p2 = p*p
LO, HI, LMAXEXP = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])

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
for t in range(LO | 1, HI, 2):
    L = has_certificate(t)
    if L == 0:
        nocert.append(t)
        print("no certificate: t = %d (t - 1 = 2^%d * %d, t - 3 = 2^%d * %d)" % (
            t, ZZ(t - 1).valuation(2), ZZ(t - 1) >> ZZ(t - 1).valuation(2),
            ZZ(t - 3).valuation(2) if t != 3 else -1, (ZZ(t - 3) >> ZZ(t - 3).valuation(2)) if t != 3 else 0))
        sys.stdout.flush()
    else:
        hist[L] = hist.get(L, 0) + 1
print("odd t in [%d, %d): certificate length histogram %s" % (LO, HI, sorted(hist.items())))
print("t without certificate up to L = 2^%d (%d values): %s" % (LMAXEXP, len(nocert), nocert))
