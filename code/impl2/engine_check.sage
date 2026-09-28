# The GF2X engine against honest integer arithmetic. Run from code/impl2/.
# (a) pent_poly(L) == prod_{n=1}^{L-1} (1 - q^n) mod 2, product expanded over ZZ by FLINT (no Euler theorem).
# (b) F(t, L) == (prod (1 - q^n))^t mod 2 with the integer power computed by PARI (eta series), t in a list.
# (c) consistency with the binary digit reduction: F(t) == prod over digits 2^i of t of f_1(q^{2^i}) mod 2.
load("lib.sage")
ok = True
L = 3000
S.<y> = PolynomialRing(ZZ)
prod_int = S(1)
for n in range(1, L):
    prod_int = (prod_int * (1 - y^n)).truncate(L)
Pz = R([c % 2 for c in prod_int.list()])
if Pz != pent_poly(L):
    ok = False; print("FAIL (a) pentagonal series")
else:
    print("(a) pentagonal series mod 2 = integer product, L =", L)

L2 = 1500
ts = list(range(1, 80, 2)) + [199, 203, 205, 255, 257]
eta_ser = pari('Ser(eta(x + O(x^%d)))' % L2)
for t in ts:
    s = eta_ser^t
    coeffs = [ZZ(s.polcoef(n)) % 2 for n in range(L2)]
    if R(coeffs) != F(t, L2):
        ok = False; print("FAIL (b) t =", t)
print("(b) F(t, %d) = integer power mod 2 (PARI eta series) for" % L2, len(ts), "values of t up to", max(ts))

L3 = 20000
for t in [5, 7, 51, 199, 203, 1025, 4097, 12345, 2^14 + 3]:
    G = R(1)
    i = 0
    while (t >> i) > 0:
        if (t >> i) & 1:
            G = (G * R({e * 2^i: 1 for e in pent_poly(L3).exponents() if e * 2^i < L3})).truncate(L3)
        i += 1
    if G != F(t, L3):
        ok = False; print("FAIL (c) t =", t)
print("(c) digit factorisation agrees with plain powering, L =", L3)
print("ENGINE CHECK:", "PASS" if ok else "FAIL")
