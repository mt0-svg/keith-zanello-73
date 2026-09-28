# The certificate tree at p = 97 with the GF2X engine of lib.sage (same node rules as search_p73_h3.sage).
# Run from code/impl2/. Starts at level KSTART = 15 (all odd tau < 2^15) with mu = 300; kztree started at level 14 with
# mu = 3000 (code/impl1/out/tree_p97.txt), so this is a second certificate with other parameters. Closure and the
# centre conditions are monotone in the level, and the sparse balls tau = 1, 3 are settled at every level >= K0.
# K0 = 11 (tau = 1) and 9 (tau = 3) are recomputed in sparse_p97.gp.
load("lib.sage")
import sys
p = 97
p2 = p * p
GOOD = [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 29, 31, 35, 37, 41, 43, 47, 57, 63, 103, 107, 115, 119,
        121, 133, 391]
K0 = {1: 11, 3: 9}
KSTART, KMAX = 15, 26
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
        k, len(nodes), cnt["closed"], cnt["lemma2"], cnt["sparse"], cnt["split"], sorted(splitlist)[:40]))
    sys.stdout.flush()
    nodes = nxt
    k += 1
if nodes:
    print("OPEN nodes remain at level %d: %s" % (k, nodes[:50])); ok = False
print("Lemma 2 centers (t, level):", sorted(centers))
used = set(c[0] for c in centers)
missing = [t for t in GOOD if t >= 5 and t not in used]
print("listed t >= 5 not used as centers:", missing)
print("TREE p = 97:", "PASS" if ok and not missing else "FAIL")
