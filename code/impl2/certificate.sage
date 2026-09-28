# The code of certificate_p73.sage run at another prime, with only the parameters changed: p from the command line,
# kappa = 2p, mu = 3000, and kstart and the list read from the first line of ../impl1/out/tree_p<p>.txt.
# Run from code/impl2/ as  sage certificate.sage P [tree]
# (a) K0 and K0' by the exact quadratic bound (Remark 16(1)).
# (b) the reduced sparse test (Remark 16(2)): for every e in <2> mod p (not mod p^2), every odd w mod 2^j (2^j > mu)
#     and every class rho mod p, some M in [Mmin, mu] with c_w(M) = 1 and some class c mod p containing two small
#     theta exponents distinct mod p^2 satisfy c + e M = rho mod p.
# (c) only with the argument "tree": the search from level kstart with the ball rule, node counts to compare with
#     ../impl1/out/tree_p<p>.txt. The per-node data is computed by two worker processes.
load("lib.sage")
import sys
p = int(sys.argv[1]); p2 = p * p; kap = 2 * p; mu = 3000
DOTREE = len(sys.argv) > 2 and sys.argv[2] == "tree"
hdr = open("../impl1/out/tree_p%d.txt" % p).readline()
KSTART = int(hdr.split("kstart=")[1].split()[0])
GOOD = [int(s) for s in hdr.split("good=")[1].strip().split(",")]
print("p = %d, kstart = %d, %d listed t" % (p, KSTART, len(GOOD)))
ok = True

# (a)
def k0_exact(tri):
    X = var('X')
    for K in range(1, 80):
        x = 2^K
        if tri:
            L = 2*x - kap - 1
            h = (2*X - kap - 1)*(2*X - kap)/2 - mu*X - kap*(kap + 1)/2
            valid = L >= 1
        else:
            y = (2*x - 3*kap - 1)/3
            L = ceil(y)
            h = (2*X - 3*kap - 1)*(2*X - 3*kap - 2)/6 - mu*X - (3*kap^2 + kap)/2
            valid = L >= 1 and y >= 1/6
        dh = diff(h, X)
        if valid and h.subs(X=x) > 0 and dh.subs(X=x) > 0:
            return K
K0 = {1: k0_exact(False), 3: k0_exact(True)}
Mmin = {tau: ceil(p2 / 2^K0[tau]) for tau in (1, 3)}
print("(a) kappa = %d, mu = %d: K0 = %s, Mmin = %s" % (kap, mu, K0, Mmin))

# (b)
j = 0
while 2^j <= mu:
    j += 1
eps = sorted(set(power_mod(2, K, p) for K in range(p)))
full = (1 << p) - 1
def rot(mask, a):
    a %= p
    return ((mask << a) | (mask >> (p - a))) & full
Pmu = pent_poly(mu + 1)
for tau in (1, 3):
    if tau == 1:
        small = [k*(3*k - 1)//2 for k in range(-kap, kap + 1)]
    else:
        small = [k*(k + 1)//2 for k in range(kap + 1)]
    byc = {}
    for s in small:
        byc.setdefault(s % p, set()).add(s % p2)
    dmask = sum(1 << c for c in byc if len(byc[c]) >= 2)
    nfail = 0; minM = 10^9
    G = Pmu
    Pw = Pmu
    P2 = Pmu.power_trunc(2, mu + 1)
    for w in range(1, 2^j, 2):
        if w > 1:
            Pw = (Pw * P2).truncate(mu + 1)
        Ms = [M for M in Pw.exponents() if Mmin[tau] <= M <= mu]
        minM = min(minM, len(Ms))
        mres = set(M % p for M in Ms)
        for e in eps:
            cov = 0
            for m in mres:
                cov |= rot(dmask, e * m)
            if cov != full:
                nfail += 1
    print("(b) tau = %d: %d classes with two small exponents distinct mod p^2, |<2> mod p| = %d, odd w mod 2^%d: %d, reduced failures %d, min #M per w %d" % (
        tau, bin(dmask).count("1"), len(eps), j, 2^(j-1), nfail, minM))
    if nfail:
        ok = False
    sys.stdout.flush()
# engine check for the iterated powers: P^w for a few w by power_trunc
for w in [1, 3, 5, 1001, 4095]:
    assert Pmu.power_trunc(w, mu + 1) == F(w, mu + 1)

# (c)
def in_ball(tau, k):
    return (k >= K0[1] and tau % 2^K0[1] == 1) or (k >= K0[3] and tau % 2^K0[3] == 3)
if not DOTREE:
    print("NEW PARAMETERS (a, b only):", "PASS" if ok else "FAIL"); sys.exit()
@parallel(ncpus=2)
def _data(chunk, k):
    L = 2^k; out = []
    for tau in chunk:
        if in_ball(tau, k):
            out.append((tau, None, None)); continue
        supp = odd_support(F(tau, L), p2)
        nop = classes_without_pair(supp, p)
        rt = rho_of(tau, p)
        out.append((tau, nop, any(N % p == rt for N in supp)))
    return out
nodes = list(range(1, 2^KSTART, 2)); k = KSTART; centers = []
while nodes and k <= KSTART + 10:
    L = 2^k; nxt = []; cnt = {"closed": 0, "lemma2": 0, "sparse": 0, "split": 0}; spl = []
    chunks = [nodes[i::64] for i in range(64)]
    data = {}
    for (_, res) in _data([(c, k) for c in chunks if c]):
        for (tau, nop, hasrt) in res:
            data[tau] = (nop, hasrt)
    assert len(data) == len(nodes)
    for tau in nodes:
        if in_ball(tau, k):
            cnt["sparse"] += 1; continue
        nop, hasrt = data[tau]
        if not nop:
            if tau in GOOD:
                print("CONTRADICTION: listed t = %d closed at level %d" % (tau, k)); ok = False
            cnt["closed"] += 1; continue
        if tau in GOOD and tau >= 5:
            rt = rho_of(tau, p)
            if set(nop) <= {rt} and hasrt:
                cnt["lemma2"] += 1; centers.append((tau, k)); continue
        cnt["split"] += 1; spl.append(tau); nxt += [tau, tau + L]
    print("(c) level %d: nodes %d, closed %d, lemma2 %d, sparse %d, split %d %s" % (
        k, len(nodes), cnt["closed"], cnt["lemma2"], cnt["sparse"], cnt["split"], sorted(spl)))
    sys.stdout.flush()
    nodes = nxt; k += 1
if nodes:
    print("OPEN nodes:", nodes[:40]); ok = False
print("(c) centers:", sorted(centers))
if sorted(set(c[0] for c in centers)) != [t for t in GOOD if t >= 5]:
    ok = False
print("NEW PARAMETERS:", "PASS" if ok else "FAIL")
