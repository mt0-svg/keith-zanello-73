\\ Level 9 lead for Lemma 11 (lem:sturm) of paper/main.tex.
\\ Claim checked: eta(3z)^8 = q f_3^8 is the newform 9.4.a.a in S_4(Gamma_0(9)),
\\ eta(3z)^8 == eta(24z) (mod 2) coefficientwise, and at p = 73 the parity test
\\ heckeCoeff(p,t,m) = a_t(pm) + a_t(m/p) == 0 (mod 2) passes for m <= 4t and far
\\ beyond (m <= 20t) exactly for the t >= 5 of E73, and fails below 4t otherwise.
\\ Run: gp -q level9_lead.gp < /dev/null      (verdict: last line RESULT PASS / FAIL)
default(parisizemax, 2000000000);
default(nbthreads, 1);

E73 = [1,3,5,7,9,11,13,15,17,19,21,23,51,55,59,61,65,69,199,203];
P = 73;
TMAX = 249;          \\ odd t < 250
MULT = 20;           \\ check m <= MULT * t for the good t
NMAX = (P*MULT*TMAX - 1)\24 + 2;   \\ c_t(n) needed up to (P m - t)/24
C = vector(TMAX);    \\ C[t] = parities of c_t(0..NMAX)

\\ f_1 mod 2 as a 0/1 vector: generalized pentagonal numbers
pent(N) =
{
  my(v = vector(N+1), a, b);
  v[1] = 1;
  for(j = 1, N, a = j*(3*j-1)/2; if(a > N, break); v[a+1] = 1 - v[a+1];
    b = j*(3*j+1)/2; if(b <= N, v[b+1] = 1 - v[b+1]));
  v;
}
tovec(S, N) = vector(N+1, n, lift(polcoef(S, n-1)));
aa(t, m) = if(m < t || (m - t) % 24, 0, if((m-t)/24 > NMAX, error("NMAX too small"), C[t][(m-t)/24 + 1]));
hk(p, t, m) = (aa(t, p*m) + if(m % p, 0, aa(t, m/p))) % 2;
firstodd(p, t, M) =
{
  for(m = 1, M, if(hk(p, t, m), return(m)));
  0;
}
initC() =
{
  my(f1, f2, cur);
  f1 = Mod(1,2) * Ser(pent(NMAX), 'x, NMAX + 1);
  f2 = subst(f1, 'x, 'x^2) + O('x^(NMAX+1));
  cur = f1;
  forstep(t = 1, TMAX, 2, C[t] = tovec(cur, NMAX); if(t < TMAX, cur = cur * f2));
}
heckecheck(D, t) =
{
  my(mft, F, G, cg, mism = 0, nz = 0, M = 4*t + 20, inS);
  mft = mfinit([9, 4*t], 1); F = mfpow(D, t);
  G = mfhecke(mft, F, P);
  cg = mfcoefs(G, M);
  inS = (mftobasis(mft, G, 1) != []);
  for(m = 1, M, if((cg[m+1] - hk(P, t, m)) % 2, mism++); if(cg[m+1] % 2, nz++));
  print("t = ", t, ": T_73 eta(3z)^(8t) in S_", 4*t, "(Gamma_0(9)): ", inS,
        "; parity mismatches with heckeCoeff for m <= ", M, ": ", mism, "; odd coefficients: ", nz);
  mism == 0 && inS;
}
main() =
{
  my(ok = 1, mf, D, B, co, cd, ce, N, bad, good, S, r, t, E = Set(E73));

  \\ 1. eta(3z)^8 in S_4(Gamma_0(9)) and its q-expansion
  mf = mfinit([9, 4], 1);
  D = mffrometaquo(Mat([3, 8]));
  print("dim S_4(Gamma_0(9)) = ", mfdim(mf), "; dim M_4(Gamma_0(9)) = ", mfdim([9,4],4));
  print("eta(3z)^8 parameters [N,k,chi,...] = ", mfparams(D));
  B = mftobasis(mf, D, 1);
  if(B == [], print("FAIL: eta(3z)^8 not in S_4(Gamma_0(9))"); ok = 0,
    print("eta(3z)^8 in S_4(Gamma_0(9)): coordinates ", B));
  co = mfcoefs(D, 20);
  print("eta(3z)^8 = ", co);
  cd = mfcoefs(mfeigenbasis(mf)[1], 20);
  if(co != cd, print("FAIL: not the eigenform"); ok = 0, print("equals the unique newform (LMFDB 9.4.a.a)"));

  \\ 2. congruence eta(3z)^8 == eta(24z) mod 2, up to q^2000
  N = 2000;
  cd = mfcoefs(D, N);
  ce = mfcoefs(mffrometaquo(Mat([24, 1])), N);
  bad = 0; for(n = 1, N+1, if((cd[n] - ce[n]) % 2, bad++));
  print("eta(3z)^8 - eta(24z): odd coefficients up to q^", N, ": ", bad);
  if(bad, ok = 0);

  \\ 3. parities c_t(n) mod 2 for odd t <= TMAX, n <= NMAX
  initC();
  print("parities of c_t(n) computed for odd t <= ", TMAX, ", n <= ", NMAX);

  \\ 3a. good t >= 5: no odd value for m <= MULT * t
  good = [];
  for(i = 1, #E73, t = E73[i]; if(t >= 5,
    r = firstodd(P, t, MULT * t);
    if(r, print("FAIL good t = ", t, ": odd at m = ", r); ok = 0, good = concat(good, t))));
  print("t >= 5 in E73 with heckeCoeff(73,t,m) even for all m <= ", MULT, "t: ", good, " (", #good, " values)");

  \\ 3b. every odd t < 250 outside E73 fails at some m <= 4t
  S = []; bad = 0;
  forstep(t = 1, TMAX, 2, if(!setsearch(E, t),
    r = firstodd(P, t, 4 * t);
    if(!r, print("FAIL bad t = ", t, ": no odd value up to 4t"); bad++, S = concat(S, [[t, r]]))));
  print("odd t < 250 outside E73: ", #S + bad, " values; failing at some m <= 4t: ", #S, "; not failing: ", bad);
  print("largest ratio (first odd m)/(4t): ", vecmax(vector(#S, i, S[i][2] / (4 * S[i][1]))) * 1.);
  print("[t, first odd m] for the first ten: ", S[1..10]);
  if(bad, ok = 0);

  \\ 4. PARI's own Hecke operator on S_{4t}(Gamma_0(9)), good t = 5..15 and bad t = 25, 27, 29 (t = 51 exceeds 2 GB)
  foreach([5, 7, 9, 13, 15, 25, 27, 29], t, if(!heckecheck(D, t), ok = 0));

  print(if(ok, "RESULT PASS", "RESULT FAIL"));
}
main();
quit;
