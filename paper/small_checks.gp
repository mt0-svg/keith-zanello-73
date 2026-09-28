\\ Small checks for the numbers quoted in main.tex (PARI/GP 2.17). Run: gp -q small_checks.gp
default(parisizemax, "2G");
default(nbthreads, 1);

\\ 1. Introduction, t = 25 at p = 73: every class mod 73 holds at least two odd c_25(N)
\\    with 5329 <= N <= 6762, and 6762 is the least such bound.
f = Vec(lift(Mod(1, 2) * eta(x + O(x^6763))^25));
cnt(B) = vecmin(vector(73, r, sum(N = 5329, B, (N % 73 == r - 1) * f[N + 1])));
print("t=25, p=73: min #odd per class, N in [5329,6762]: ", cnt(6762), "  (bound 6761: ", cnt(6761), ")");

\\ 2. Bases r_t = -t/24 mod p^2.
rt(p, t) = lift(Mod(-t, p^2) / 24);
print("r_5, r_69 at 73: ", rt(73, 5), ", ", rt(73, 69), "   24*222 = ", 24 * 222, ", 24*392 = ", 24 * 392);
print("24*1110 + 5 = ", 24 * 1110 + 5, " = 5*73^2: ", 24 * 1110 + 5 == 5 * 73^2);

\\ 3. The counterexample for t = 5 at p = 29.
g = Vec(eta(x + O(x^205))^5);
print("c_5(204) = ", g[205], ", r_5 mod 29^2 = ", rt(29, 5), ", 24*204+5 = ", factor(24 * 204 + 5));

\\ 4. Divisor-sum formula of Proposition t5: c_5(N) = S(24N+5)/2 mod 2 for N < 20000.
S(m) = sumdiv(m, d, kronecker(-4, d));
h = Vec(lift(Mod(1, 2) * eta(x + O(x^20000))^5));
print("c_5(N) = S(24N+5)/2 mod 2 for all N < 20000: ", prod(N = 0, 19999, (S(24 * N + 5) / 2 - h[N + 1]) % 2 == 0));

\\ 5. Sturm bound and the largest index used in step 1.
print("index of Gamma_0(576) = ", 576 * 3 / 2 * 4 / 3, ";  (t+1)/2 * 1152/12 = 48(t+1)");
print("max N in step 1: p=73 (t=203): ", (73 * 48 * 204 - 203) \ 24, ", p=97 (t=391): ", (97 * 48 * 392 - 391) \ 24);

\\ 6. K0 by the exact quadratic test (Remark rem:check (1)), M_min, orders of 2, double classes.
k0(kap, mu, tri) = {
  for (k = 1, 61,
    my(X = 2^k, ok);
    if (tri,
      my(l = 2 * X - kap - 1);
      ok = l >= 1 && l * (l + 1) - 2 * mu * X - kap * (kap + 1) > 0 && 4 * X - 2 * kap - 1 - mu > 0,
      my(a = 3 * kap + 1, n = 2 * X - a);
      ok = n >= 1 && n * (n - 1) - 6 * mu * X - 3 * (3 * kap^2 + kap) > 0 && 8 * X - 4 * a - 2 - 6 * mu > 0);
    if (ok, return(k)));
  error("no K0");
}
dbl(p, tri) = {
  my(kap = 2 * p, Sv, c = vector(p));
  Sv = if (tri, Set(vector(kap + 1, i, ((i - 1) * i / 2) % p^2)),
               Set(vector(2 * kap + 1, i, my(j = i - kap - 1); (j * (3 * j - 1) / 2) % p^2)));
  for (i = 1, #Sv, c[Sv[i] % p + 1]++);
  #select(v -> v >= 2, c);
}
{
  foreach([73, 97], p,
    my(K1 = k0(2 * p, 3000, 0), K3 = k0(2 * p, 3000, 1));
    print("p=", p, ": K0=", K1, " K0'=", K3, " Mmin=", ceil(p^2 / 2^K1), ",", ceil(p^2 / 2^K3),
          " ord_p(2)=", znorder(Mod(2, p)), " ord_p^2(2)=", znorder(Mod(2, p^2)),
          " double classes=", dbl(p, 0), ",", dbl(p, 1)));
}
h1(X) = my(kap = 146, a = 3 * kap + 1); (2 * X - a) * (2 * X - a - 1) - 6 * 3000 * X - 3 * (3 * kap^2 + kap);
h3(X) = my(kap = 146); (2 * X - kap - 1) * (2 * X - kap) - 2 * 3000 * X - kap * (kap + 1);
print("p=73: h1(2^12) = ", h1(2^12), ", h1(2^13) = ", h1(2^13), ", h3(2^10) = ", h3(2^10), ", h3(2^11) = ", h3(2^11));
print("p=73 with mu=300: K0=", k0(146, 300, 0), " K0'=", k0(146, 300, 1), ";  p=97 with mu=300: K0=", k0(194, 300, 0), " K0'=", k0(194, 300, 1));

\\ 7. H_t = eta(z)^2 eta(24z)^t / eta(2z): holomorphic modular form, level, weight, character,
\\    and H_t = eta(24z)^t mod 2 up to q^2000, for every t >= 5 in E_73 and E_97.
E73 = [5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 51, 55, 59, 61, 65, 69, 199, 203];
E97 = [5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 29, 31, 35, 37, 41, 43, 47, 57, 63, 103, 107, 115, 119, 121, 133, 391];
chkH(t) = {
  my(F = mffrometaquo([1, 2; 2, -1; 24, t]), P, c, a);
  if (F == 0, return("not holomorphic"));
  P = mfparams(F);
  c = mfcoefs(F, 2000);
  a = Vec(lift(Mod(1, 2) * eta(x + O(x^((2000 - t) \ 24 + 1)))^t));
  for (m = 0, 2000,
    my(am = if (m >= t && (m - t) % 24 == 0, a[(m - t) / 24 + 1], 0));
    if ((c[m + 1] - am) % 2, return(Str("mismatch at ", m))));
  [P[1], P[2], P[3]];
}
{
  my(bad = 0, lev = Set(), chr = Set());
  foreach(setunion(Set(E73), Set(E97)), t,
    my(r = chkH(t));
    if (type(r) == "t_STR" || r[2] != (t + 1) / 2, bad++; print("t=", t, ": ", r),
      lev = setunion(lev, [r[1]]); chr = setunion(chr, [r[3]])));
  print("H_t checks for t in E_73 u E_97 (t >= 5): failures ", bad, ", levels ", lev, ", characters ", chr);
}

\\ 8. Members of the family a + b 2^e (a, b in {1,3}, e > 0) in E_73.
E73all = concat([1, 3], E73);
fam = Set(concat(vector(4, i, vector(20, e, [1, 1, 3, 3][i] + [1, 3, 1, 3][i] * 2^e))));
print("family members in E_73: ", setintersect(fam, Set(E73all)));
