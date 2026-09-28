# The 2-adic certificate tree at p = 73, recomputed with the GF2X engine. Run from code/impl2/.
# Node (tau, k): tau odd, tau < 2^k, stands for all odd 2-adic T = tau mod 2^k.
# F_T mod x^{2^k} = f_1^tau mod (2, x^{2^k}) for every such T (f_1^{2^k} = 1 mod x^{2^k}).
# Settled if: closed (every class mod p has two odd indices N in [p^2, 2^k) distinct mod p^2), or
# Lemma 13 (tau listed, tau >= 5: every class except rho_tau has such a pair and class rho_tau has an odd
# index N in [p^2, 2^k)), or tau in {1, 3} at level k >= K0 (10 resp. 9, recomputed in sparse_p73.gp).
load("lib.sage")
import sys
p = 73
p2 = p * p
GOOD = [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 51, 55, 59, 61, 65, 69, 199, 203]
K0 = {1: 10, 3: 9}
KSTART, KMAX = 3, 22
nodes = [tau for tau in range(1, 2^KSTART, 2)]
k = KSTART
ok = True
centers = []
while nodes and k <= KMAX:
    L = 2^k
    nxt = []
    cnt = {"closed": 0, "lemma2": 0, "sparse": 0, "split": 0}
    splitlist = []
    for tau in nodes:
        if tau in K0 and k >= K0[tau]:
            cnt["sparse"] += 1
            continue
        supp = odd_support(F(tau, L), p2)
        nopair = classes_without_pair(supp, p)
        if not nopair:
            if tau in GOOD:
                print("CONTRADICTION: listed t = %d is closed (bad) at level %d" % (tau, k)); ok = False
            cnt["closed"] += 1
            continue
        if tau in GOOD and tau >= 5:
            rt = rho_of(tau, p)
            if set(nopair) <= {rt} and any(N % p == rt for N in supp):
                cnt["lemma2"] += 1
                centers.append((tau, k))
                continue
        cnt["split"] += 1
        splitlist.append(tau)
        nxt += [tau, tau + L]
    print("level %d: nodes %d, closed %d, lemma2 %d, sparse %d, split %d %s" % (
        k, len(nodes), cnt["closed"], cnt["lemma2"], cnt["sparse"], cnt["split"],
        sorted(splitlist)[:40] if k >= 13 else ""))
    sys.stdout.flush()
    nodes = nxt
    k += 1
if nodes:
    print("OPEN nodes remain at level %d: %s" % (k, nodes[:50])); ok = False
print("Lemma 2 centers (t, level):", sorted(centers))
used = set(c[0] for c in centers)
missing = [t for t in GOOD if t >= 5 and t not in used]
print("listed t >= 5 not used as centers:", missing)
# negative control: a pretend-good t must not pass as a centre (Lemma 13) if it is actually closed
print("TREE:", "PASS" if ok and not missing else "FAIL")
