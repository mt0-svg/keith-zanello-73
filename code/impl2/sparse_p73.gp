\\ Lemma 15 (sparse points 1 and 3) at p = 73, kappa = 146, mu = 300. Run from code/impl2/.
\\ (a) K0: least K such that the size condition holds for every K' >= K, proved through a quadratic lower bound.
\\ (b) for every e in <2> mod p^2 and every odd w mod 2^j (2^j > mu), the special indices
\\     N = 2^K M + s (c_w(M) odd, Mmin <= M <= mu, s in the small theta exponents) give a pair in every class mod p.
\\ Coefficients c_w(M) mod 2 from PARI series arithmetic over Z/2 (third engine, independent of GF2X and ser2).
\\ Marked residue sets are bitmasks (t_INT) of p^2 bits; union over a in A of the rotation of the small set by a.
default(parisizemax, 2000000000)
default(nbthreads, 1)
{
my(p = 73, p2 = 73^2, kap = 146, mu = 300, allok = 1, K0 = [0, 0], Mmin = [0, 0]);
\\ ---------- (a) K0 ----------
for (tri = 0, 1,
  my(holds = (K) -> my(X = 2^K, L);
      if (tri, L = 2*X - kap - 1; L >= 1 && L*(L+1)/2 > X*mu + kap*(kap+1)/2,
               L = ceil((2*X - 3*kap - 1)/3); L >= 1 && (3*L^2 - L)/2 > X*mu + (3*kap^2 + kap)/2));
  \\ lower bound h(X) valid for real X with L >= 1, a quadratic in X with positive leading coefficient
  my(hp = if (tri, ('X - kap/2 - 1/2)*(2*'X - kap) - 'X*mu - kap*(kap+1)/2,
                   (2*'X - 3*kap - 1)*(2*'X - 3*kap - 2)/6 - 'X*mu - (3*kap^2 + kap)/2));
  my(dh = deriv(hp, 'X), k0 = 0);
  for (K = 1, 60, if (holds(K) && subst(hp, 'X, 2^K) > 0 && subst(dh, 'X, 2^K) > 0 &&
        (if (tri, 2*2^K - kap - 1 >= 1, 2*2^K - 3*kap - 1 >= 3)), k0 = K; break));
  \\ minimality: the exact condition fails at k0 - 1 (not needed for validity, recorded)
  my(fails_before = !holds(k0 - 1));
  K0[tri + 1] = k0; Mmin[tri + 1] = ceil(p2 / 2^k0);
  printf("tau = %d: K0 = %d (exact condition fails at K0 - 1: %d), h(X) = %s, Mmin = %d\n",
         2*tri + 1, k0, fails_before, hp, Mmin[tri + 1]);
  \\ the proof for all K >= K0: h is a quadratic with positive leading coefficient, h(2^K0) > 0, h'(2^K0) > 0,
  \\ and the exact left side is >= h(2^K) because (3L^2 - L)/2 is increasing for L >= 1 and L >= (2X - 3 kap - 1)/3.
  if (pollead(hp) <= 0, allok = 0; print("FAIL: leading coefficient"));
);
\\ ---------- (b) the finite check ----------
my(j = 0); while (2^j <= mu, j++);
my(E = Mod(1, 2) * Ser(eta('q + O('q^(mu + 1))), 'q));
\\ control: E is the pentagonal series mod 2
my(pent = sum(k = -30, 30, 'q^(k*(3*k-1)/2)) + O('q^(mu+1)));
if (E != Mod(1,2)*pent, allok = 0; print("FAIL: eta series mod 2 is not pentagonal"));
my(es = List(), e = 1); until (e == 1, listput(es, e); e = 2*e % p2);
printf("|<2> mod p^2| = %d, j = %d, odd w mod 2^j: %d\n", #es, j, 2^(j-1));
my(MASK = 2^p2 - 1, C = 2^p - 1);
for (tri = 0, 1,
  my(small = if (tri, vector(kap + 1, i, my(k = i - 1); (k*(k+1)/2) % p2),
                      vector(2*kap + 1, i, my(k = i - 1 - kap); (k*(3*k-1)/2) % p2)));
  my(S = 0); for (i = 1, #small, S = bitor(S, 2^small[i]));
  my(nfail = 0, ncombo = 0, minA = 10^9);
  forstep (w = 1, 2^j - 1, 2,
    my(Fw = E^w, Ms = List());
    for (M = Mmin[tri + 1], mu, if (polcoef(Fw, M, 'q) != 0, listput(Ms, M)));
    minA = min(minA, #Ms);
    for (ie = 1, #es,
      my(e = es[ie], mk = 0);
      for (i = 1, #Ms, my(a = e * Ms[i] % p2);
        mk = bitor(mk, bitor(bitand(shift(S, a), MASK), shift(S, a - p2))));
      my(ones = 0, twos = 0);
      for (i = 0, p - 1, my(c = bitand(shift(mk, -p*i), C)); twos = bitor(twos, bitand(ones, c)); ones = bitor(ones, c));
      ncombo++;
      if (twos != C, nfail++; if (nfail <= 5, printf("  failure tau=%d e=%d w=%d\n", 2*tri+1, e, w)));
    );
  );
  printf("tau = %d: combos checked %d, failures %d, min #special M per w = %d\n", 2*tri + 1, ncombo, nfail, minA);
  if (nfail > 0, allok = 0);
);
\\ ---------- negative control: the same test with the small set reduced to {0} must fail somewhere ----------
my(S0 = 1, nf0 = 0, Fw = E^1, Ms = List());
for (M = 6, mu, if (polcoef(Fw, M, 'q) != 0, listput(Ms, M)));
for (ie = 1, #es, my(e = es[ie], mk = 0);
  for (i = 1, #Ms, my(a = e * Ms[i] % p2); mk = bitor(mk, bitor(bitand(shift(S0, a), MASK), shift(S0, a - p2))));
  my(ones = 0, twos = 0);
  for (i = 0, p - 1, my(c = bitand(shift(mk, -p*i), C)); twos = bitor(twos, bitand(ones, c)); ones = bitor(ones, c));
  if (twos != C, nf0++));
printf("negative control (small set {0}, w = 1): failures %d of %d (must be > 0)\n", nf0, #es);
if (nf0 == 0, allok = 0);
print("SPARSE CHECK: ", if (allok, "PASS", "FAIL"));
}
