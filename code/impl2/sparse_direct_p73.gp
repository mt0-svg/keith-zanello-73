\\ The sparse region (Lemma 15) by direct counting, with no use of Lemma 15. Run from code/impl2/ as
\\   gp -q -D parisizemax=3000000000 -D nbthreads=1 sparse_direct_p73.gp
\\ For T = tau + 2^K w (tau in {1, 3}, K >= 2, w odd): mod 2, F_T = F_tau(q) F_w(q^(2^K)), with
\\ F_1 = sum over generalised pentagonal P of q^P (Euler) and F_3 = f_1^3 = sum over triangular numbers (Jacobi), so
\\   c_T(N) = #{(P, M) : P in supp F_tau, M in supp F_w, N = P + 2^K M} mod 2.
\\ Part 1: for the t listed without certificate in spot_p73.out and brute_p73.out, the full odd support of f_1^T
\\         below Nmax = 2^K (MU + 1) by enumerating all pairs (P, M), then a pair in every class mod 73
\\         (two odd indices N >= 73^2, distinct mod 73^2); smallest length L at which such a certificate exists.
\\ Part 2: every index of every certificate of part 1 recounted by square tests (24x + 1, 8x + 1).
\\ Part 3: certificates for T = tau + 2^K w at large K (all K in [K0, K0 + 656], every residue of 2^K mod 73^2,
\\         plus sparse K up to 3000) built from candidate indices N = 2^K M + s, each one's parity computed by
\\         the full count over all M' in supp F_w, M' <= N / 2^K (not by Lemma 15).
p = 73; p2 = p^2; MU = 300;
pent(B) = {my(v = List(), k = 0);
  while (k*(3*k-1)/2 <= B, listput(v, k*(3*k-1)/2); if (k > 0 && k*(3*k+1)/2 <= B, listput(v, k*(3*k+1)/2)); k++);
  vecsort(Vec(v));}
tri(B) = {my(v = List(), k = 0); while (k*(k+1)/2 <= B, listput(v, k*(k+1)/2); k++); Vec(v);}
\\ support of F_w mod 2 below B+1, from the pentagonal polynomial raised to the power w over F_2 (series)
suppw(w, B) = {my(P = Mod(1, 2) * (sum(i = 1, #pent(B), 'q^(pent(B)[i])) + O('q^(B + 1))), G = P^w, v = List());
  for (M = 0, B, if (polcoef(G, M, 'q) != 0, listput(v, M))); Vec(v);}
istheta(tau, x) = if (x < 0, 0, if (tau == 1, issquare(24*x + 1), issquare(8*x + 1)));
fullcount(tau, K, S, N) = {my(c = 0, X = 2^K); for (i = 1, #S, if (X*S[i] > N, break); c += istheta(tau, N - X*S[i])); c % 2;}

\\ ---------- Part 1 ----------
oddsupp(tau, K, w, Nmax) = {
  my(th = if (tau == 1, pent(Nmax - 1), tri(Nmax - 1)), S = suppw(w, (Nmax - 1) >> K), X = 2^K, n = 0, v, j = 0, out = List());
  for (i = 1, #S, for (a = 1, #th, if (th[a] + X*S[i] < Nmax, n++, break)));
  v = vectorsmall(n);
  for (i = 1, #S, for (a = 1, #th, my(N = th[a] + X*S[i]); if (N < Nmax, j++; v[j] = N, break)));
  v = vecsort(v);
  my(i = 1); while (i <= n, my(k = i); while (k < n && v[k + 1] == v[i], k++); if ((k - i + 1) % 2, listput(out, v[i])); i = k + 1);
  [Vec(out), S];
}
certify(odd) = {my(first = vector(p, i, -1), pr = vector(p, i, 0), done = 0, Lneed = 0);
  for (i = 1, #odd, my(N = odd[i]); if (N < p2, next);
    my(rho = N % p + 1);
    if (pr[rho] != 0, next);
    if (first[rho] == -1, first[rho] = N, if (N % p2 != first[rho] % p2, pr[rho] = [first[rho], N]; done++; Lneed = max(Lneed, N + 1)));
    if (done == p, break));
  if (done < p, return([0, vector(p, r, if (pr[r] == 0, r - 1, -1))]));
  [Lneed, pr];}
allok = 1;

\\ ---------- Part 0: validation of oddsupp and fullcount against dense series (PARI, t_SER over Z/2) ----------
{
my(Nv = 12000, Pd = Mod(1, 2) * (sum(i = 1, #pent(Nv), 'q^(pent(Nv)[i])) + O('q^Nv)), nbad = 0, nctl = 0);
foreach ([[1, 10, 3], [3, 9, 5], [1, 4, 1], [3, 5, 3], [1, 3, 7], [3, 11, 1]], c,
  my(tau = c[1], K = c[2], w = c[3], T = tau + 2^K * w, D = Pd^T, r = oddsupp(tau, K, w, Nv), S = suppw(w, Nv >> K), dense = List(), mis = 0);
  for (N = 0, Nv - 1, if (polcoef(D, N, 'q) != 0, listput(dense, N)));
  if (Vec(dense) != r[1], mis++);
  for (N = 0, Nv - 1, if (fullcount(tau, K, S, N) != (polcoef(D, N, 'q) != 0), mis++; break));
  nbad += mis;
  printf("Part 0: T = %d = %d + 2^%d * %d: oddsupp and fullcount vs dense series on N < %d: %s (%d odd coefficients)\n", T, tau, K, w, Nv, if (mis, "MISMATCH", "equal"), #dense));
\\ control: below K0 the special-index shortcut is false, so fullcount must differ from c_w(M) somewhere
my(S = suppw(1, 1200), sm = vecsort(vector(2*146 + 1, i, my(k = i - 1 - 146); k*(3*k-1)/2), , 8));
for (M = 0, 60, my(cw = #select(x -> x == M, S)); for (a = 1, #sm, if (fullcount(1, 5, S, 2^5*M + sm[a]) != cw, nctl++)));
printf("Part 0 control: tau = 1, K = 5 (< K0): special indices with full count != c_w(M): %d (must be > 0)\n", nctl);
if (nbad || !nctl, allok = 0);
}
{T1 = [[1, 13, 1], [3, 13, 1], [1, 14, 1], [3, 14, 1], [1, 15, 1], [3, 15, 1], [1, 14, 3], [3, 14, 3],
      [1, 20, 1], [1, 22, 1], [3, 20, 1], [3, 21, 1]];
for (i = 1, #T1, my(tau = T1[i][1], K = T1[i][2], w = T1[i][3], T = tau + 2^K * w, Nmax = 2^K * (MU + 1));
  my(r = oddsupp(tau, K, w, Nmax), odd = r[1], S = r[2], c = certify(odd));
  if (c[1] == 0,
    allok = 0; printf("t = %d = %d + 2^%d * %d: NO certificate below %d; classes without a pair: %s\n", T, tau, K, w, Nmax, select(x -> x >= 0, c[2])),
    my(pr = c[2], bad = 0, mx = 0);
    for (rho = 1, p, for (u = 1, 2, my(N = pr[rho][u]); mx = max(mx, N); if (fullcount(tau, K, S, N) != 1, bad++)));
    if (bad, allok = 0);
    printf("t = %d = %d + 2^%d * %d: %d odd coefficients below %d; certificate needs L = %d = 2^%d * %.3f (M up to %d); square-test recount of the 146 indices: %s; class 0: %s\n",
      T, tau, K, w, #odd, Nmax, c[1], K, c[1] / 2.^K, floor(mx / 2^K), if (bad, Str("MISMATCH ", bad), "OK"), pr[1]));
);}

\\ ---------- Part 3 ----------
kap = 146;
smallset(tau) = if (tau == 1, vecsort(vector(2*kap + 1, i, my(k = i - 1 - kap); k*(3*k-1)/2), , 8), vector(kap + 1, i, (i-1)*i/2));
K0v = [10, 9]; Mminv = [6, 11];
direct(tau, K, w) = {
  my(sm = smallset(tau), S = suppw(w, MU + 64), X = 2^K, first = vector(p, i, -1), done = 0, ncand = 0, mm = Mminv[(tau + 1)/2]);
  for (i = 1, #S, my(M = S[i]); if (M < mm, next); if (M > MU, break);
    for (a = 1, #sm, my(N = X*M + sm[a], rho = N % p + 1);
      if (first[rho] == -2, next);
      if (first[rho] != -1 && N % p2 == first[rho], next);
      ncand++;
      if (N < p2 || fullcount(tau, K, S, N) != 1, next);
      if (first[rho] == -1, first[rho] = N % p2, first[rho] = -2; done++);
      if (done == p, return([1, ncand]))));
  [0, ncand];}
nf3 = 0; nc3 = 0; mx3 = 0;
Ks(tau) = concat(vector(657, i, K0v[(tau + 1)/2] + i - 1), [700, 701, 1000, 1500, 2047, 2048, 3000]);
{
for (tau = 1, 3, if (tau == 2, next);
  foreach ([1, 3, 5, 7, 255, 511, 12345, 2^20 + 1], w,
    my(Kl = if (w <= 3, Ks(tau), select(K -> (K % 7 == 0) || K < K0v[(tau + 1)/2] + 20, Ks(tau))), nfail = 0);
    for (i = 1, #Kl, my(r = direct(tau, Kl[i], w)); nc3++; mx3 = max(mx3, r[2]);
      if (!r[1], nfail++; if (nfail <= 5, printf("  Part 3 FAILURE tau = %d K = %d w = %d\n", tau, Kl[i], w))));
    nf3 += nfail;
    printf("Part 3: tau = %d, w = %d: %d values of K in [%d, 3000], failures %d\n", tau, w, #Kl, Kl[1], nfail)));
printf("Part 3: %d combinations, failures %d, largest number of full counts used %d\n", nc3, nf3, mx3);
if (nf3, allok = 0);
print("SPARSE DIRECT: ", if (allok, "PASS", "FAIL"));
}
quit;
