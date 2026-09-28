\\ The six odd t in [2^16, 2^18) left without certificate by brute_p73_range.sage (cap L = 2^19), by the direct
\\ pair count of sparse_direct_p73.gp Part 1 (same functions, copied), with the square-test recount of every index.
\\ Run from code/impl2/ as gp -q -D parisizemax=2500000000 -D nbthreads=1 leftovers_p73.gp
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
{T1 = [[1, 16, 1], [3, 16, 1], [1, 17, 1], [3, 17, 1], [1, 16, 3], [3, 16, 3]];
for (i = 1, #T1, my(tau = T1[i][1], K = T1[i][2], w = T1[i][3], T = tau + 2^K * w, Nmax = 2^K * (MU + 1));
  my(r = oddsupp(tau, K, w, Nmax), odd = r[1], S = r[2], c = certify(odd));
  if (c[1] == 0,
    allok = 0; printf("t = %d = %d + 2^%d * %d: NO certificate below %d; classes without a pair: %s\n", T, tau, K, w, Nmax, select(x -> x >= 0, c[2])),
    my(pr = c[2], bad = 0, mx = 0);
    for (rho = 1, p, for (u = 1, 2, my(N = pr[rho][u]); mx = max(mx, N); if (fullcount(tau, K, S, N) != 1, bad++)));
    if (bad, allok = 0);
    printf("t = %d = %d + 2^%d * %d: %d odd coefficients below %d; certificate needs L = %d = 2^%d * %.3f; square-test recount of the 146 indices: %s\n",
      T, tau, K, w, #odd, Nmax, c[1], K, c[1] / 2.^K, if (bad, Str("MISMATCH ", bad), "OK")));
);
print("LEFTOVERS: ", if (allok, "PASS", "FAIL"));}
quit;
