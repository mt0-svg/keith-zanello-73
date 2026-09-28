# Goodness of the listed t >= 5 at p = 97 (Lemma 11, Sturm bound 48(t+1)), same test as sturm_p73.sage,
# with negative controls for the odd t < 400 not listed. Run from code/impl2/.
load("lib.sage")
p = 97
GOOD = [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 29, 31, 35, 37, 41, 43, 47, 57, 63, 103, 107, 115, 119,
        121, 133, 391]

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
    print("t = %d: Sturm bound %d, T_p G_t = 0 mod 2 up to the bound: %s" % (t, B, not bad))
    if bad:
        ok = False
ctrl = [t for t in range(5, 400, 2) if t not in GOOD and not hecke_zero(t, 48 * (t + 1))]
print("negative controls (odd t < 400 not listed) with T_p G_t = 0 up to the bound:", ctrl)
if ctrl:
    ok = False
print("STURM p = 97:", "PASS" if ok else "FAIL")
