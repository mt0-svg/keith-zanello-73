# Goodness of the listed t >= 5 at p = 73 (Lemma 11). Run from code/impl2/.
# G_t = eta(24z)^t = sum_N c_t(N) q^{24N+t}; a(m) = c_t((m-t)/24) if m >= t, m = t mod 24, else 0.
# Mod 2, T_p G_t has coefficients b(m) = a(pm) + [p | m] a(m/p).
# (a) b(m) = 0 for 1 <= m <= 48(t+1) (Sturm bound for weight (t+1)/2 on Gamma_0(576));
# (b) numerical extension: b(m) = 0 for m <= 4 * 48(t+1);
# (c) negative controls: the same test must fail for the odd t < 240 not in the list.
# (d) PARI's mf package: level, weight and character of eta(24z)^t * theta(z).
load("lib.sage")
p = 73
GOOD = [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 51, 55, 59, 61, 65, 69, 199, 203]

def hecke_zero(t, B):
    L = (p * B - t) // 24 + 2
    G = F(t, L)
    def a(m):
        if m < t or (m - t) % 24 != 0:
            return 0
        return int(G[(m - t) // 24])
    bad = []
    for m in range(1, B + 1):
        b = a(p * m)
        if m % p == 0:
            b ^^= a(m // p)
        if b:
            bad.append(m)
            if len(bad) >= 3:
                break
    return bad

ok = True
for t in GOOD:
    if t < 5:
        continue
    B = 48 * (t + 1)
    bad = hecke_zero(t, B)
    bad4 = hecke_zero(t, 4 * B)
    print("t = %d: Sturm bound %d, T_p G_t = 0 mod 2 up to bound: %s; up to 4x bound: %s" % (t, B, not bad, not bad4))
    if bad or bad4:
        ok = False
ctrl_fail = []
for t in range(5, 240, 2):
    if t in GOOD:
        continue
    if not hecke_zero(t, 48 * (t + 1)):
        ctrl_fail.append(t)
print("negative controls (odd t < 240 not listed) where T_p G_t = 0 up to the bound:", ctrl_fail)
if ctrl_fail:
    ok = False

# (d) level and character through PARI mf (eta(24z)^t as an eta quotient, theta = mfTheta)
for t in [5, 7, 9, 11, 13, 23, 51, 69, 199, 203]:
    res = pari('my(f = mfmul(mffrometaquo([24, %d]), mfTheta())); mfparams(f)' % t)
    print("t = %d: mfparams(eta(24z)^t theta) = %s" % (t, res))
print("STURM CHECK:", "PASS" if ok else "FAIL")
