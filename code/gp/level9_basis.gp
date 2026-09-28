\\ Weight 2 Eisenstein forms on Gamma_0(9) that give an integral triangular basis of
\\ M_{2j}(Gamma_0(9)), and W = H0*G + G^2 == eta(24z) (mod 2).
\\   H0  = (3 E2(3z) - E2(z))/2 = 1 + 12 sum (s1(n) - 3 s1(n/3)) q^n
\\   H0p = (9 E2(9z) - E2(z))/8 = 1 + 3 sum (s1(n) - 9 s1(n/9)) q^n
\\   G   = sum chi(n) s1(n) q^n, chi = (-3/.)  (= E2 twisted by chi, E_2^{chi,chi})
\\   F2  = (H0 - H0p - 9 G)/54                 (claimed integral, q^2 + O(q^3))
\\ Run: gp -q level9_basis.gp < /dev/null      (verdict: last line RESULT PASS / FAIL)
default(parisizemax, 1000000000);
default(nbthreads, 1);
NB = 3000;
s1(n) = if(denominator(n) != 1 || n < 1, 0, sigma(n));
chi(n) = kronecker(-3, n);
coefH0(n)  = if(n == 0, 1, 12*(s1(n) - 3*s1(n/3)));
coefH0p(n) = if(n == 0, 1, 3*(s1(n) - 9*s1(n/9)));
coefG(n)   = if(n == 0, 0, chi(n)*s1(n));
ser(f) = sum(n = 0, NB, f(n)*'q^n) + O('q^(NB+1));
inspace(mf, S) =
{
  my(v = vector(NB+1, n, polcoef(S, n-1)), c, F, w);
  c = mftobasis(mf, v, 1);
  if(c == [], return(0));
  F = mflinear(mf, c); w = mfcoefs(F, NB);
  w == v;
}
main() =
{
  my(ok = 1, mf2, H0, H0p, G, F2, W, E, bad, nonint, D, mf4, Q, orders, j, B, piv);
  mf2 = mfinit([9, 2], 4);
  print("dim M_2(Gamma_0(9)) = ", mfdim(mf2), ", dim S_2 = ", mfdim([9,2],1));
  H0 = ser(coefH0); H0p = ser(coefH0p); G = ser(coefG);
  F2 = (H0 - H0p - 9*G)/54;
  foreach([["H0", H0], ["H0p", H0p], ["G", G], ["F2", F2]], x,
    my(r = inspace(mf2, x[2])); print(x[1], " in M_2(Gamma_0(9)) (all ", NB, " coefficients match): ", r); if(!r, ok = 0));
  nonint = 0; for(n = 0, NB, if(denominator(polcoef(F2, n)) != 1, nonint++));
  print("F2 = ", truncate(F2 + O('q^8)), " ...; non-integral coefficients up to q^", NB, ": ", nonint);
  if(nonint, ok = 0);
  \\ G against PARI's E_2^{chi,chi}
  E = mfeisenstein(2, Mod(2,3), Mod(2,3));
  print("G / E_2(chi,chi) coefficient ratio check: ", mfcoefs(E, 12), " vs ", vector(13, n, coefG(n-1)));
  \\ W = H0*G + G^2 == eta(24z) mod 2
  W = H0*G + G^2;
  D = mfcoefs(mffrometaquo(Mat([24, 1])), NB);
  bad = 0; for(n = 0, NB, if((polcoef(W, n) - D[n+1]) % 2, bad++));
  print("W = H0*G + G^2 in M_4(Gamma_0(9)): ", inspace(mfinit([9,4],4), W), "; W - eta(24z) odd coefficients up to q^", NB, ": ", bad);
  if(bad, ok = 0);
  \\ triangular basis in weight 2j: H0^a G^b F2^c, a+b+c = j, order b + 2c, leading coefficient 1
  foreach([2, 10, 50], j,
    piv = 1;
    for(i = 0, 2*j, my(c = i\2, b = i%2, a = j - b - c, M = H0^a * G^b * F2^c, v = valuation(M, 'q));
      if(v != i || polcoef(M, i) != 1, piv = 0));
    print("weight ", 2*j, ": monomials H0^a G^b F2^c give orders 0..", 2*j, " with leading coefficient 1: ", piv);
    if(!piv, ok = 0));
  \\ eta-quotient alternative in weight 4 (orders 0..4), for the record
  mf4 = mfinit([9, 4], 4);
  Q = [Mat([1,12;3,-4]), Mat([3,8]), Mat([1,6;3,-4;9,6]), Mat([1,3;3,-4;9,9]), Mat([3,-4;9,12])];
  orders = vector(#Q, i, my(F = mffrometaquo(Q[i]), c = mfcoefs(F, 10), v = 0); while(c[v+1] == 0, v++);
    [v, c[v+1], mftobasis(mf4, F, 1) != []]);
  print("weight 4 eta quotients [order, leading coefficient, in M_4(Gamma_0(9))]: ", orders);
  print(if(ok, "RESULT PASS", "RESULT FAIL"));
}
main();
quit;
