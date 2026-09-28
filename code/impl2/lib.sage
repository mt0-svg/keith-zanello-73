# Library of the second implementation (written independently of code/impl1/rust/src/ser2.rs and kztree.rs).
# Engine: f_1 mod 2 = sum_{k in Z} q^{k(3k-1)/2} as an element of GF(2)[x] (NTL GF2X), and
# f_1^t mod (2, x^L) by plain truncated powering P^t (no binary digit factorisation is used).
R.<x> = PolynomialRing(GF(2))

def pent_poly(L):
    """f_1 mod 2 truncated at x^L, from Euler's pentagonal theorem (exponents k(3k-1)/2, k in Z)."""
    ex = set()
    k = 0
    while k*(3*k-1)//2 < L:
        ex.add(k*(3*k-1)//2)          # k >= 0
        v = k*(3*k+1)//2              # value at -k
        if v < L:
            ex.add(v)
        k += 1
    return R({e: 1 for e in ex})

_Pcache = {}
def F(t, L):
    """f_1^t mod (2, x^L), t >= 0 an integer."""
    if L not in _Pcache:
        _Pcache[L] = pent_poly(L)
    P = _Pcache[L]
    if t == 0:
        return R(1)
    return P.power_trunc(t, L)

def odd_support(G, Nmin=0):
    """Exponents N >= Nmin with coefficient 1."""
    return [e for e in G.exponents() if e >= Nmin]

def classes_without_pair(supp, p):
    """supp: indices (all assumed >= p^2). Return the classes rho mod p that do NOT contain two indices
    distinct mod p^2."""
    p2 = p*p
    seen = [set() for _ in range(p)]
    for N in supp:
        seen[N % p].add(N % p2)
    return [rho for rho in range(p) if len(seen[rho]) < 2]

def rho_of(t, p):
    return (-t * inverse_mod(24, p)) % p

def r_of(t, p):
    return (-t * inverse_mod(24, p*p)) % (p*p)
