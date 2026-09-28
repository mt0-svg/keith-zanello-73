# Goodness of the listed t >= 5 at a prime p (Lemma 11), adapted from sturm_p73.sage. Run from code/impl2/:
#   sage sturm.sage <p> <control bound>
# The good list is read from the first line of ../impl1/out/tree_p<p>.txt.
# G_t = eta(24z)^t = sum_N c_t(N) q^{24N+t}; a(m) = c_t((m-t)/24) if m >= t, m = t mod 24, else 0.
# Mod 2, T_p G_t has coefficients b(m) = a(pm) + [p | m] a(m/p).
# (a) b(m) = 0 for 1 <= m <= 48(t+1) (Sturm bound for weight (t+1)/2 on Gamma_0(576));
# (b) numerical extension: b(m) = 0 for m <= 2 * 48(t+1);
# (c) negative controls: the same test must fail below the bound for every odd 5 <= t < control bound not listed;
# (d) PARI mfparams of eta(24z)^t theta(z) for a few listed t.
load("lib.sage")
import sys, time
p = int(sys.argv[1]); CB = int(sys.argv[2])
line = open("../impl1/out/tree_p%d.txt" % p).readline()
GOOD = [int(s) for s in line.split("good=")[1].split(",")]
print("p = %d, %d listed t: %s" % (p, len(GOOD), GOOD))
t0 = time.time()

def hecke_bad(t, B, maxbad=3):
    L = (p * B - t) // 24 + 2
    G = F(t, L)
    def a(m):
        if m < t or (m - t) % 24 != 0:
            return 0
        return int(G[(m - t) // 24])
    bad = []
    # only m with p*m = t mod 24 can give a(pm) != 0; m/p term needs p | m
    for m in range(1, B + 1):
        b = a(p * m)
        if m % p == 0:
            b ^^= a(m // p)
        if b:
            bad.append(m)
            if len(bad) >= maxbad:
                break
    return bad

ok = True
for t in GOOD:
    if t < 5:
        continue
    B = 48 * (t + 1)
    bad = hecke_bad(t, B)
    bad2 = hecke_bad(t, 2 * B)
    print("t = %d: Sturm bound %d, T_p G_t = 0 mod 2 up to bound: %s; up to 2x bound: %s" % (t, B, not bad, not bad2))
    sys.stdout.flush()
    if bad or bad2:
        ok = False
print("[%.1f s]" % (time.time() - t0))
ctrl_fail = []; nctrl = 0; maxfirst = 0
for t in range(5, CB, 2):
    if t in GOOD:
        continue
    nctrl += 1
    bad = hecke_bad(t, 48 * (t + 1), 1)
    if not bad:
        ctrl_fail.append(t)
    else:
        maxfirst = max(maxfirst, bad[0])
print("negative controls: %d odd t in [5, %d) not listed; those where T_p G_t = 0 up to the bound: %s; largest first failure index m = %d" % (nctrl, CB, ctrl_fail, maxfirst))
if ctrl_fail:
    ok = False
print("[%.1f s]" % (time.time() - t0))
sample = sorted(set([t for t in GOOD if t >= 5][:3] + [t for t in GOOD if t >= 5][-3:]))
for t in sample:
    res = pari('my(f = mfmul(mffrometaquo([24, %d]), mfTheta())); mfparams(f)' % t)
    print("t = %d: mfparams(eta(24z)^t theta) = %s" % (t, res))
print("STURM CHECK p = %d:" % p, "PASS" if ok else "FAIL")
