\\ Search a representation criterion p = x^2 + n y^2 (optionally y odd) matching a set of primes.
\\ Evidence tool only: compares sets of primes p = 1 mod 24 below PMAX.
\\ No default() here: a default() inside a file loaded with read() skips the rest of the file; set it in the caller.
PMAX = 1500;
PL = select(p -> isprime(p), vector((PMAX - 73) \ 24 + 1, i, 73 + 24*(i-1)));
rep(p, n, par) = {  \\ par: 0 any y != 0, 1 y odd, 2 y even (y != 0)
  for (y = 1, sqrtint(p \ n), my(r = p - n*y^2); if (issquare(r) && (par == 0 || (par == 1 && y % 2) || (par == 2 && y % 2 == 0)), return(1)));
  0;
}
search(S, NMAX) = {
  my(tgt = vector(#PL, i, setsearch(S, PL[i]) > 0), res = List());
  for (n = 1, NMAX, for (par = 0, 2,
    my(v = vector(#PL, i, rep(PL[i], n, par)));
    if (v == tgt, listput(res, [n, par, "="]));
    if (v == vector(#PL, i, 1 - tgt[i]), listput(res, [n, par, "complement"]))));
  Vec(res);
}
